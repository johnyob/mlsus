open! Import
module F = Structure.Former
module R = Structure.Rigid (F)

module Region = struct
  (** The [Generalization] module manages the generalisation of graphical types.

      Each type belongs to a 'region', which indicates where those types are
      existentially bound in the solver's stack. *)
  type 'a t =
    { mutable status : status
    ; mutable types : 'a list
    ; mutable rigid_vars : 'a list
    ; raise_scope_escape : 'a -> unit
    }
  [@@deriving sexp_of]

  and status =
    | Not_generalized (** A region that is yet to be generalized *)
    | Partially_generalized (** A region that is 'partially' generalized *)
    | Fully_generalized (** A region that is ('fully') generalized *)
  [@@deriving sexp_of]

  let create ~raise_scope_escape () =
    { raise_scope_escape; types = []; rigid_vars = []; status = Not_generalized }
  ;;

  let register_type t type_ = t.types <- type_ :: t.types
  let register_rigid_var t rigid_var = t.rigid_vars <- rigid_var :: t.rigid_vars

  module Tree = struct
    type 'a node = 'a t Tree.node [@@deriving sexp_of]
    type nonrec 'a t = 'a t Tree.t [@@deriving sexp_of]

    (** A type used to trick ppx_sexp_conv *)
    type 'a sexp_identifier_node = 'a node

    let sexp_of_sexp_identifier_node _sexp_of_a (node : 'a sexp_identifier_node) =
      [%sexp_of: Identifier.t] node.id
    ;;

    let region (t : 'a node) = t.value
  end
end

(** A match identifier is a uid allocated for each suspended match *)
module Match_identifier = Identifier

(** An instance identifier is a uid allocated for each instance *)
module Instance_identifier = Identifier

(** There are two kinds of guards:
    1. Match guards -- these are unique and introduced by suspended matches.
        They indicate that the variable may be unified by a handler of a suspended match.

    2. Instance guards -- introduced by instantiating a partial generic.
       They indicate that the variable may be unified by propagation via a partial generic.

    The guard graph [G] is formed by (labeled) edges between types and instance groups.

    A 'match' edge is introduced by a match guard [m] between two types [t1] and [t2], written
    [t1 <-[m]- t2]. We read this as 't2 is guarded by t1 using match m'

    A 'instance' edge is introduced by an instance group [j] and an instance type [t], written
    [t <-[j]- .]. We read this as 't is guarded by the partial instance group j'. It is useful to note
    that a cycle in the graph can never arise from an instance group (by construction). The [.] here denotes
    a 'root'.
*)
module Guard = struct
  module Match = struct
    type t = Match [@@deriving equal, compare, sexp, hash]
  end

  module Instance = struct
    type t = Instance [@@deriving equal, compare, sexp, hash]
  end

  module T = struct
    type 'a t =
      | Match : Match_identifier.t -> Match.t t
      | Instance : Instance_identifier.t -> Instance.t t
    [@@deriving sexp_of]
  end

  include T

  module Packed = struct
    module T = struct
      type t = T : 'a T.t -> t [@@deriving sexp_of]

      let t_of_sexp _ = assert false

      let compare (T t1) (T t2) =
        match t1, t2 with
        | Match _, Instance _ -> -1
        | Instance _, Match _ -> 1
        | Match mid1, Match mid2 -> Match_identifier.compare mid1 mid2
        | Instance iid1, Instance iid2 -> Instance_identifier.compare iid1 iid2
      ;;
    end

    include T
    include Comparable.Make (T)
  end

  let pack (type a) (t : a t) : Packed.t = T t

  module Map : sig
    (** ['s] the parameter that match guards store in the map *)
    type 's t [@@deriving sexp_of]

    module Key = T

    module Data : sig
      type ('s, 'a) t =
        | Match : 's -> ('s, Match.t) t
        | Instance : ('s, Instance.t) t
      [@@deriving sexp_of]
    end

    val empty : _ t
    val singleton : 'a Key.t -> ('s, 'a) Data.t -> 's t
    val is_empty : _ t -> bool
    val mem : _ t -> _ Key.t -> bool
    val add : 's t -> key:'a Key.t -> data:('s, 'a) Data.t -> [ `Ok of 's t | `Duplicate ]
    val set : 's t -> key:'a Key.t -> data:('s, 'a) Data.t -> 's t
    val remove : 's t -> 'a Key.t -> 's t
    val merge_skewed : 's t -> 's t -> 's t
    val is_subset : 's t -> of_:'s t -> bool
    val key_set : _ t -> Packed.Set.t
    val remove_many : 's t -> Packed.Set.t -> 's t

    module Match : sig
      val is_empty : _ t -> bool
      val iter : 's t -> f:(key:Match_identifier.t -> data:'s -> unit) -> unit
    end
  end = struct
    module Key = T

    module Data = struct
      type ('s, 'a) t =
        | Match : 's -> ('s, Match.t) t
        | Instance : ('s, Instance.t) t
      [@@deriving sexp_of]
    end

    type 's t =
      { match_map : 's Match_identifier.Map.t
      ; inst_set : Instance_identifier.Set.t
      }
    [@@deriving sexp_of]

    let sexp_of_t _sexp_of_a t =
      [%sexp_of: Match_identifier.Set.t * Instance_identifier.Set.t]
        (Map.key_set t.match_map, t.inst_set)
    ;;

    let empty =
      { match_map = Match_identifier.Map.empty; inst_set = Instance_identifier.Set.empty }
    ;;

    let is_empty t = Map.is_empty t.match_map && Set.is_empty t.inst_set

    let is_subset t1 ~of_:t2 =
      is_empty t1
      || (Set.is_subset (Map.key_set t1.match_map) ~of_:(Map.key_set t2.match_map)
          && Set.is_subset t1.inst_set ~of_:t2.inst_set)
    ;;

    let key_set t =
      Set.union
        (Packed.Set.map (Map.key_set t.match_map) ~f:(fun mid -> pack (Match mid)))
        (Packed.Set.map t.inst_set ~f:(fun iid -> pack (Instance iid)))
    ;;

    let mem (type s a) (t : s t) (key : a Key.t) =
      match key with
      | Match mid -> Map.mem t.match_map mid
      | Instance iid -> Set.mem t.inst_set iid
    ;;

    let add (type s a) (t : s t) ~(key : a Key.t) ~(data : (s, a) Data.t)
      : [ `Ok of s t | `Duplicate ]
      =
      match key, data with
      | Match mid, Match data ->
        (match Map.add t.match_map ~key:mid ~data with
         | `Ok match_map -> `Ok { t with match_map }
         | `Duplicate -> `Duplicate)
      | Instance iid, Instance -> `Ok { t with inst_set = Set.add t.inst_set iid }
    ;;

    let set (type s a) (t : s t) ~(key : a Key.t) ~(data : (s, a) Data.t) : s t =
      match key, data with
      | Match mid, Match data -> { t with match_map = Map.set t.match_map ~key:mid ~data }
      | Instance iid, Instance -> { t with inst_set = Set.add t.inst_set iid }
    ;;

    let remove (type s a) (t : s t) (key : a Key.t) =
      match key with
      | Match mid -> { t with match_map = Map.remove t.match_map mid }
      | Instance iid -> { t with inst_set = Set.remove t.inst_set iid }
    ;;

    let remove_many t key_set =
      Set.fold key_set ~init:t ~f:(fun t (Packed.T key) -> remove t key)
    ;;

    let singleton (type s a) (key : a Key.t) (data : (s, a) Data.t) = set empty ~key ~data

    let merge_skewed t1 t2 =
      { match_map =
          Map.merge_skewed t1.match_map t2.match_map ~combine:(fun ~key:_ type1 _type2 ->
            type1)
      ; inst_set = Set.union t1.inst_set t2.inst_set
      }
    ;;

    module Match = struct
      let iter t ~f = Map.iteri t.match_map ~f
      let is_empty t = Map.is_empty t.match_map
    end
  end
end

module Partial_status = struct
  type 'a t =
    { region_node : 'a Region.Tree.sexp_identifier_node
    ; instances : 'a Instance_identifier.Map.t
    ; kind : kind
    }
  [@@deriving sexp_of]

  and kind =
    | Instance
    | Generic
  [@@deriving sexp_of]

  let merge t1 t2 ~unify =
    { region_node = Tree.nearest_common_ancestor t1.region_node t2.region_node
    ; instances =
        (* Any instances from the same group *must* be equal *)
        Map.merge_skewed t1.instances t2.instances ~combine:(fun ~key:_ type1 type2 ->
          unify type1 type2;
          type1)
    ; kind =
        (* Any form of update to statuses maps to an instance.
           [generalize_young_region] uses this bit to determine if we need to propagate
           types to the instances. *)
        Instance
    }
  ;;
end

module Status = struct
  type 'a t =
    | Instance of 'a Region.Tree.sexp_identifier_node
    | Partial of 'a Partial_status.t
    | Generic
  [@@deriving sexp_of]

  let set_region t rn =
    match t with
    | Instance _ -> Instance rn
    | Partial p -> Partial { p with region_node = rn }
    | Generic -> Generic
  ;;

  let region t =
    match t with
    | Instance rn -> Some rn
    | Partial { region_node = rn; _ } -> Some rn
    | Generic -> None
  ;;

  let merge t1 t2 ~unify ~partial_unify =
    match t1, t2 with
    | Generic, _ | _, Generic -> assert false
    | Partial p1, Partial p2 -> Partial (Partial_status.merge p1 p2 ~unify)
    | Instance rn1, Partial { region_node = rn2; instances; kind = _ }
    | Partial { region_node = rn1; instances; kind = _ }, Instance rn2 ->
      Map.iteri instances ~f:(fun ~key ~data -> partial_unify key data);
      Instance (Tree.nearest_common_ancestor rn1 rn2)
    | Instance rn1, Instance rn2 ->
      (* Computing the nearest common ancestor is indeed necessary here.

         Consider three regions arrangled like this:

             R0
            /  \
           R1  R2

         - In R0, we have the variable 'a
         - In R1, we unify 'a with 'b list
         - In R2, we unify 'a with 'c list list

         This implies that: 'b = 'c list.

         However:
         - 'c list has the status [Instance R2]
         - 'b has the status [Instance R1]

         On unifying 'b and 'c list, we must lower the rank of
         'b to [Instance R0], the nearest common ancestor of R1
         and R2. *)
      Instance (Tree.nearest_common_ancestor rn1 rn2)
  ;;

  let of_region_node region_node =
    match (Region.Tree.region region_node).status with
    | Not_generalized -> Instance region_node
    | Partially_generalized ->
      Partial { region_node; instances = Instance_identifier.Map.empty; kind = Instance }
    | Fully_generalized -> assert false
  ;;

  let is_generic t =
    match t with
    | Generic -> true
    | Partial _ | Instance _ -> false
  ;;
end

module S = struct
  module Inner = Structure.Suspended_first_order (R)

  type 'a t =
    { id : Identifier.t
    ; inner : 'a Inner.t
    ; guards : 'a Guard.Map.t
    ; removed_guards : Guard.Packed.Set.t
    ; status : 'a Status.t
    }
  [@@deriving sexp_of]

  let create ~id_source ~region_node inner =
    { id = Identifier.create id_source
    ; status = Status.of_region_node region_node
    ; guards = Guard.Map.empty
    ; removed_guards = Guard.Packed.Set.empty
    ; inner
    }
  ;;

  let add_guard t ~guard ~data =
    { t with
      guards = Guard.Map.set t.guards ~key:guard ~data
    ; removed_guards = Set.remove t.removed_guards (Guard.Packed.T guard)
    }
  ;;

  let remove_guard t guard =
    { t with
      guards = Guard.Map.remove t.guards guard
    ; removed_guards = Set.add t.removed_guards (Guard.Packed.T guard)
    }
  ;;

  let flexize t =
    match t.inner with
    | Structure Rigid_var -> { t with inner = Var Empty }
    | _ -> t
  ;;

  let is_generalizable t =
    let has_no_handlers =
      match t.inner with
      | Var (Empty_one_or_more_handlers _) -> false
      | _ -> true
    in
    let is_unguarded = Guard.Map.is_empty t.guards in
    is_unguarded && has_no_handlers
  ;;

  let generalize t =
    let if_unguarded_then_generalize ~else_ =
      if is_generalizable t
      then flexize { t with status = Generic }
      else { t with status = else_ }
    in
    match t.status with
    | Generic -> assert false
    | Partial { kind = Generic; _ } ->
      (* [generalize] cannot generalize partial generics. See [partial_generalize] *)
      t
    | Partial ({ kind = Instance; instances; _ } as ps) when not (Map.is_empty instances)
      ->
      (* [generalize] cannot generalize partial instances with non-empty instance maps.
         See [generalize_young_region] *)
      { t with status = Partial { ps with kind = Generic } }
    | Partial ({ kind = Instance; _ } as ps) ->
      if_unguarded_then_generalize ~else_:(Partial { ps with kind = Generic })
    | Instance region_node ->
      if_unguarded_then_generalize
        ~else_:
          (Partial
             { region_node; instances = Instance_identifier.Map.empty; kind = Generic })
  ;;

  let partial_generalize t ~f =
    match t.status with
    | Partial { kind = Generic; instances; region_node = _ } when is_generalizable t ->
      (* An unguarded partial generic can be generalized. [f] can be used to notify instances *)
      Map.iteri instances ~f:(fun ~key ~data -> f key data);
      flexize { t with status = Generic }
    | _ -> t
  ;;

  let partial_ungeneralize t ~f =
    match t.status with
    | Partial { kind = Instance; instances; region_node = _ } ->
      (* An ungeneralized instance that is still partial (but whose level is lowered)
         must noify the instances of this (likely making then less generic) *)
      Map.iteri instances ~f:(fun ~key ~data -> f key data)
    | _ -> ()
  ;;

  type 'a ctx =
    { id_source : Identifier.source
    ; curr_region : 'a Region.Tree.node
    ; remove_instance_guard : 'a -> Instance_identifier.t -> unit
    ; super : 'a Inner.ctx
    }

  exception Cannot_merge = Inner.Cannot_merge

  let iter t ~f = Inner.iter t.inner ~f
  let fold t ~init ~f = Inner.fold t.inner ~init ~f

  let merge ~ctx ~create:create_type ~unify ~type1 ~type2 t1 t2 =
    let create inner =
      let region_node = ctx.curr_region in
      let type_ = create_type (create ~id_source:ctx.id_source ~region_node inner) in
      Region.(register_type (Tree.region region_node) type_);
      type_
    in
    let partial_unify instance_id inst =
      (* It doesn't matter which type ([type1] or [type2]) we pick, since after
         the current unification is successful, [type1] and [type2] will refer to
         the *same* type. *)
      unify type2 inst;
      ctx.remove_instance_guard inst instance_id
    in
    let status = Status.merge t1.status t2.status ~unify ~partial_unify in
    let inner =
      Inner.merge ~ctx:ctx.super ~create ~unify ~type1 ~type2 t1.inner t2.inner
    in
    let guards = Guard.Map.merge_skewed t1.guards t2.guards in
    let removed_guards = Set.union t1.removed_guards t2.removed_guards in
    { id = t1.id; status; inner; guards; removed_guards }
  ;;

  let is_generic t = Status.is_generic t.status
end

module Scheme = struct
  type 'a t =
    { root : 'a
    ; region_node : 'a Region.Tree.sexp_identifier_node option
    }
  [@@deriving sexp_of]

  let body t = t.root
  let mono_scheme root = { root; region_node = None }
end

module Type = struct
  include Unifier.Make (S)
  include Type

  type region_node = t Region.Tree.node [@@deriving sexp_of]

  type sexp_identifier_region_node = t Region.Tree.sexp_identifier_node
  [@@deriving sexp_of]

  type region_tree = t Region.Tree.t [@@deriving sexp_of]
  type region = t Region.t [@@deriving sexp_of]
  type scheme = t Scheme.t [@@deriving sexp_of]

  let id t = (structure t).id
  let inner t = (structure t).inner

  let set_inner t inner =
    let structure = structure t in
    set_structure t { structure with inner }
  ;;

  let status t = (structure t).status

  let set_status t status =
    let structure = structure t in
    set_structure t { structure with status }
  ;;

  let region t = Status.region (status t)

  let region_exn ?here type_ =
    Option.value_exn ?here ~message:"Type cannot be generic" (region type_)
  ;;

  let set_region t region_node =
    let status = status t in
    set_status t (Status.set_region status region_node)
  ;;

  let level t = Option.(region t >>| fun r -> r.level)

  let level_exn ?here type_ =
    Option.value_exn ?here ~message:"Type cannot be generic" (level type_)
  ;;

  let generalize t =
    let structure = structure t in
    set_structure t (S.generalize structure)
  ;;

  let partial_generalize t ~f =
    let structure = structure t in
    set_structure t (S.partial_generalize structure ~f)
  ;;

  let partial_ungeneralize t ~f = S.partial_ungeneralize (structure t) ~f

  let add_guard t ~guard ~data =
    let structure = structure t in
    set_structure t (S.add_guard structure ~guard ~data)
  ;;

  let remove_guard t guard =
    let structure = structure t in
    set_structure t (S.remove_guard structure guard)
  ;;

  let add_handler t handler =
    match inner t with
    | Var svar ->
      let svar = S.Inner.Var.add_handler svar handler in
      set_inner t (Var svar)
    | Structure _ -> assert false
  ;;

  let is_generic t = S.is_generic (structure t)
  let guards t = (structure t).guards

  let set_guards t guards =
    let structure = structure t in
    set_structure t { structure with guards }
  ;;

  let removed_guards t = (structure t).removed_guards

  let set_removed_guards t removed_guards =
    let structure = structure t in
    set_structure t { structure with removed_guards }
  ;;
end

module Generalization_tree : sig
  (** Generalization can be performed lazily at instantiation. A region [rn] may
      be generalized provided all of the descendants are generalized. We represent
      this constraint as a tree of regions that need to be generalized,
      a {e generalization_tree}. Visiting a region signals that a region must be
      generalized at some point in the future.

      Note that the above implies that when generalizing the root region, all
      regions must be generalized. *)
  type t [@@deriving sexp_of]

  (** [create ()] returns an empty generalization tree. *)
  val create : root:Type.region_node -> t

  (** [is_empty t] returns whether the tree is empty (i.e. no more regions to generalize). *)
  val is_empty : t -> bool

  (** [visit_region t rn] visits a region [rn], marking it for generalization in
      the future. *)
  val visit_region : t -> Type.region_node -> unit

  (** [generalize_region t rn ~f ~finally] generalizes [rn] (and all of its decsendants that are
      to be generalized). [f rn'] is called for each generalizable region [rn']. After [f rn']
      is called, [finally ()] is called.

      Safety: [f rn] may update [t] only using [visit_region].
      [finally ()] may update [t] using [visit_region] or [generalize_region] *)
  val generalize_region
    :  t
    -> Type.region_node
    -> f:(Type.region_node -> unit)
    -> finally:(unit -> unit)
    -> unit

  (** [num_partially_generalized_regions t] returns the number of regions that are partially
      generalized. This is used to detect cycles in the generalization tree. *)
  val num_partially_generalized_regions : t -> int
end = struct
  type t =
    { entered_map : (Identifier.t, (Identifier.t, Type.region_node) Hashtbl.t) Hashtbl.t
      (** Maps node identifiers to immediate entered descendants *)
    ; mutable num_partially_generalized_regions : int
      (** Tracks the partially generalized regions. If there are remaining
          partially generalized regions after generalizing the root region, it implies
          there exists suspended matches that were never scheduled (e.g. a cycle between matches). *)
    ; root : Type.region_node
    }
  [@@deriving sexp_of]

  let incr_partially_generalized_regions t =
    t.num_partially_generalized_regions <- t.num_partially_generalized_regions + 1
  ;;

  let decr_partially_generalized_regions t =
    t.num_partially_generalized_regions <- t.num_partially_generalized_regions - 1
  ;;

  let num_partially_generalized_regions t = t.num_partially_generalized_regions

  let create ~(root : Type.region_node) =
    (* Initialize the root region + visit it *)
    let entered_map = Hashtbl.create (module Identifier) in
    Hashtbl.set entered_map ~key:root.id ~data:(Hashtbl.create (module Identifier));
    { entered_map; num_partially_generalized_regions = 0; root }
  ;;

  let is_empty t = Hashtbl.is_empty t.entered_map

  let rec find_closest_entered_ancestor t (node : Type.region_node) =
    match node.parent with
    | None -> None
    | Some parent ->
      if Hashtbl.mem t.entered_map parent.id
      then Some parent
      else find_closest_entered_ancestor t parent
  ;;

  let find_closest_entered_ancestor_or_root t node =
    match find_closest_entered_ancestor t node with
    | None when Identifier.(t.root.id <> node.id) ->
      Hashtbl.set t.entered_map ~key:t.root.id ~data:(Hashtbl.create (module Identifier));
      Some t.root
    | result -> result
  ;;

  let visit_region t (rn : Type.region_node) =
    if not (Hashtbl.mem t.entered_map rn.id)
    then (
      (* Enter [rn] *)
      let imm_descendants = Hashtbl.create (module Identifier) in
      Hashtbl.set t.entered_map ~key:rn.id ~data:imm_descendants;
      match find_closest_entered_ancestor_or_root t rn with
      | None -> assert (Identifier.(rn.id = t.root.id))
      | Some anc ->
        (* TODO: optimisation, if we know [rn] is a new region, then we can ignore this *)
        (* Reparent decendents of [rn] *)
        let anc_descendants = Hashtbl.find_exn t.entered_map anc.id in
        Hashtbl.filter_inplace anc_descendants ~f:(fun imm_descendant ->
          let imm_anc =
            find_closest_entered_ancestor t imm_descendant
            |> Option.value_exn ~here:[%here]
          in
          if Identifier.(imm_anc.id = rn.id)
          then (
            Hashtbl.set imm_descendants ~key:imm_descendant.id ~data:imm_descendant;
            false)
          else true);
        (* Register [rn] as a descendant of [anc] *)
        Hashtbl.set anc_descendants ~key:rn.id ~data:rn)
  ;;

  let remove_region t (rn : Type.region_node) =
    assert (Hashtbl.is_empty (Hashtbl.find_exn t.entered_map rn.id));
    Hashtbl.remove t.entered_map rn.id;
    match find_closest_entered_ancestor t rn with
    | None -> assert (Identifier.(t.root.id = rn.id))
    | Some anc -> Hashtbl.remove (Hashtbl.find_exn t.entered_map anc.id) rn.id
  ;;

  let generalize_region t (rn : Type.region_node) ~f ~finally =
    let rec visit : Type.region_node -> unit =
      fun rn ->
      match Hashtbl.find t.entered_map rn.id with
      | None -> ()
      | Some imm_descendants ->
        let rec loop () =
          match Hashtbl.choose imm_descendants with
          | None -> ()
          | Some (_rn_id, rn) ->
            visit rn;
            (* It is very crucial *not* to remove [rn] from [imm_descendants]
               as a region should only be removed *prior* to calling [f rn].
               It it was visited *after* calling [f rn] (or in [finally]), then
               this loop should re-generalize the region. *)
            loop ()
        in
        loop ();
        (* Remove entry :) *)
        remove_region t rn;
        (* Generalize *)
        let bft_region_status = (Region.Tree.region rn).status in
        f rn;
        (* Update number of partially_generalized regions *)
        let aft_region_status = (Region.Tree.region rn).status in
        (match bft_region_status, aft_region_status with
         | Not_generalized, Partially_generalized ->
           [%log.global.debug "Was a un-generalized region, now is partially generalized"];
           incr_partially_generalized_regions t
         | Partially_generalized, Fully_generalized ->
           [%log.global.debug
             "Was an partially generalized region, now is fully generalized"];
           decr_partially_generalized_regions t
         | Partially_generalized, Partially_generalized
         | Not_generalized, Fully_generalized -> ()
         | _, Not_generalized | Fully_generalized, _ ->
           (* Invalid region status transition *)
           assert false);
        (* Note: [f rn] may (somehow) visit [rn] (or a descendant of [rn]).
           This is safe since after this function returns, the parent region
           (if generalizing) will detect that [rn] (or a descendant of) has
           been visited and re-generalize the region.

           Additionally [finally ()] may generalize any region, since at this
           point the tree is in a valid state. *)
        finally ()
    in
    (* Note when [rn] is the root of the traversal and it gets revisited
       by [finally ()], we need to regeneralize the region. In the nested case, this
       is ensured by the [loop ()] function that iterates over immediate descendants.
       But at the root, we need to ensure this with this while loop.  *)
    while Hashtbl.mem t.entered_map rn.id do
      visit rn
    done
  ;;
end

module Scheduler : sig
  type job = unit -> unit

  (** [t] is a scheduler, a queue of [job]s that are to be run.
      When a suspended variable is filled, all of the handlers
      are scheduled. *)
  type t [@@deriving sexp_of]

  (** [create ()] returns a new scheduler *)
  val create : unit -> t

  val is_empty : t -> bool

  (** [schedule t job] schedules the [job] in the scheduler [t] *)
  val schedule : t -> job -> unit

  (** [schedule_all t jobs] schedules the [job]s in the scheduler [t]. *)
  val schedule_all : t -> job list -> unit

  (** [run t] runs {e all} jobs in [t]. *)
  val run : t -> unit
end = struct
  type job = unit -> unit
  and t = { job_queue : job Queue.t } [@@deriving sexp_of]

  let create () = { job_queue = Queue.create () }
  let is_empty t = Queue.is_empty t.job_queue
  let schedule t job = Queue.enqueue t.job_queue job
  let schedule_all t jobs = Queue.enqueue_all t.job_queue jobs

  let run t =
    let rec loop () =
      match Queue.dequeue t.job_queue with
      | None -> ()
      | Some job ->
        job ();
        loop ()
    in
    loop ()
  ;;
end

module State = struct
  type t =
    { id_source : (Identifier.source[@sexp.opaque])
    ; generalization_tree : Generalization_tree.t
    ; scheduler : Scheduler.t
    }
  [@@deriving sexp_of]

  let create_with_root_region () =
    let id_source = Identifier.create_source () in
    let rn =
      Tree.create
        ~id_source
        (Region.create
           ~raise_scope_escape:(fun _ ->
             (* The root region should *not* bind rigid variables *)
             assert false)
           ())
      |> Tree.root
    in
    let generalization_tree = Generalization_tree.create ~root:rn in
    { id_source; generalization_tree; scheduler = Scheduler.create () }, rn
  ;;
end

module Unify = Type.Make_unify (S)

module Young_region = struct
  type t =
    { region : Type.region
    ; node : Type.region_node
    ; mem : Type.t -> bool
      (** Returns [true] if given type is a member of the current region *)
    }
  [@@deriving sexp_of]

  let of_region_node region_node =
    let region = Region.Tree.region region_node in
    let mem =
      let set =
        Hash_set.of_list (module Identifier) (region.types |> List.map ~f:Type.id)
      in
      fun type_ -> Hash_set.mem set (Type.id type_)
    in
    { region; node = region_node; mem }
  ;;
end

module Guard_graph : sig
  type t

  val create : level:Tree.Level.t -> roots_and_guarded_partial_generics:Type.t list -> t

  (** [never_realized t] returns a list of lists of types where each type is never realized.

      A type is realized if it is unified with a concrete (non-variable) structure. A type is
      known to never be realized if it is in a cycle of the guard graph and an old variable is not
      reachable. *)
  val never_realized : t -> Type.t list list
end = struct
  (* When generalizing the young region, we construct a guard graph of the young
     region (and its children). Intuitively, this graph is a subgraph of the
     (implicit) global guard graph.

     This guard graph is used to compute the strongly connected components. *)

  module G = struct
    type t =
      { nodes : Type.t list
      ; young_level : Tree.Level.t
      }
    [@@deriving sexp_of]

    module Node = struct
      type t = Type.t [@@deriving sexp_of]

      (* Hash the types using the identifier *)
      let hash_fold_t state t = Identifier.hash_fold_t state (Type.id t)
      let hash = Hash.of_fold hash_fold_t
      let compare = Comparable.lift Identifier.compare ~f:Type.id
    end

    let iter_nodes t ~f = List.iter t.nodes ~f

    let iter_succ t node ~f =
      match Type.level node with
      | None ->
        (* The type is generic, it must be a root! *)
        ()
      | Some level ->
        if Tree.Level.(level < t.young_level)
        then
          (* Old nodes are considered root nodes *)
          ()
        else Guard.Map.Match.iter (Type.guards node) ~f:(fun ~key:_ ~data:succ -> f succ)
    ;;
  end

  include G
  include Scc.Make (G)

  let create ~level ~roots_and_guarded_partial_generics =
    { nodes = roots_and_guarded_partial_generics; young_level = level }
  ;;

  let never_realized t =
    let scc_roots = scc_leafs t in
    List.filter scc_roots ~f:(function
      | [ node ] ->
        (* We want to filter out any old nodes. Old nodes will always be in
           leaf SCCs of length 1 *)
        (match Type.level node with
         | None ->
           (* This is a generic leaf SCC -- it is never realized. Keep it *)
           true
         | Some level -> not Tree.Level.(level < t.young_level))
      | _ -> true)
  ;;
end

open State

let visit_region ~state rn = Generalization_tree.visit_region state.generalization_tree rn

let enter_region ~state ~raise_scope_escape curr_region =
  let rn =
    Tree.create_node
      ~id_source:state.id_source
      ~parent:curr_region
      (Region.create ~raise_scope_escape ())
  in
  visit_region ~state rn;
  rn
;;

let create_type ~state ~curr_region inner =
  let type_ =
    Type.create (S.create ~id_source:state.id_source ~region_node:curr_region inner)
  in
  Region.(register_type (Tree.region curr_region) type_);
  type_
;;

let create_var ~state ~curr_region () = create_type ~state ~curr_region (Var Empty)

let create_rigid_var ~state ~curr_region () =
  let rigid_var = create_type ~state ~curr_region (Structure Rigid_var) in
  Region.(register_rigid_var (Tree.region curr_region) rigid_var);
  rigid_var
;;

let create_former ~state ~curr_region former =
  create_type ~state ~curr_region (Structure (Structure former))
;;

let copy ~state ~curr_region ~when_ ~instance_id t =
  let copies = Hashtbl.create (module Identifier) in
  let rec loop type_ =
    let structure = Type.structure type_ in
    match structure.status with
    | Instance _ | Partial { kind = Instance; _ } -> type_
    | Generic | Partial { kind = Generic; _ } ->
      (try Hashtbl.find_exn copies structure.id with
       | Not_found_s _ ->
         let copy = create_var ~state ~curr_region () in
         Hashtbl.set copies ~key:structure.id ~data:copy;
         if when_ type_
         then (
           (match structure.status with
            | Partial { kind = Generic; instances; region_node } ->
              Type.add_guard copy ~guard:(Instance instance_id) ~data:Instance;
              Type.set_structure
                type_
                { structure with
                  status =
                    Partial
                      { kind = Generic
                      ; region_node
                      ; instances = Map.set instances ~key:instance_id ~data:copy
                      }
                }
            | Generic -> ()
            | Instance _ | Partial { kind = Instance; _ } ->
              (* Cannot instantiate instances *)
              assert false);
           Type.set_inner copy (S.Inner.copy ~f:loop structure.inner));
         copy)
  in
  loop t
;;

let partial_copy ~state ~curr_region ~instance_id partial_type =
  copy
    ~state
    ~curr_region
    ~instance_id
    ~when_:(fun type_ ->
      (* Always copy the root structure of the partial type *)
      Type.same_class partial_type type_
      ||
      (* Copy generics fully, partial generics are shallowly copied (only fresh vars)
         if they're already part of this instance group *)
      match Type.status type_ with
      | Generic -> true
      | Partial { kind = Generic; instances; _ } -> not (Map.mem instances instance_id)
      | Partial { kind = Instance; _ } | Instance _ -> assert false)
    partial_type
;;

let unify ~state ~curr_region type1 type2 =
  let schedule_handler s (handler : _ S.Inner.Var.handler) =
    Scheduler.schedule state.scheduler (fun () -> handler.run s)
  in
  let remove_instance_guard instance instance_id =
    (* Must visit region since instance may be partially generialized *)
    visit_region ~state (Type.region_exn ~here:[%here] instance);
    Type.remove_guard instance (Instance instance_id)
  in
  let unifier_ctx : _ S.ctx =
    { id_source = state.id_source
    ; curr_region
    ; remove_instance_guard
    ; super = { schedule_handler; super = () }
    }
  in
  Unify.unify ~ctx:unifier_ctx type1 type2
;;

let update_type_levels ~state (young_region : Young_region.t) =
  [%log.global.debug "Updating types" (young_region : Young_region.t)];
  let visited = Hash_set.create (module Identifier) in
  let rec loop type_ r =
    (* Invariant: [r.level <= young_region.level]

       This is guaranteed by the region invariant (scopes can only increase). *)
    [%log.global.debug "Visiting" (type_ : Type.t) (r : Type.sexp_identifier_region_node)];
    let r' = Type.region_exn ~here:[%here] type_ in
    [%log.global.debug "Region of type_" (r' : Type.sexp_identifier_region_node)];
    let id = Type.id type_ in
    if Hash_set.mem visited id
    then (
      [%log.global.debug "Already visited" (id : Identifier.t)];
      assert (Tree.Level.(r'.level <= r.level)))
    else (
      [%log.global.debug "Not previously visited" (id : Identifier.t)];
      Hash_set.add visited id;
      [%log.global.debug "Marked as visited"];
      (* Visiting and updating region *)
      (* Invariant: [r] and [r'] lie on a given path from the root region.

         This is guaranteed by scoping invariants. This invariant ensures that
         these regions can be compared by levels. *)
      if Tree.compare_node_by_level r r' < 0
      then (
        visit_region ~state r;
        Type.set_region type_ r;
        [%log.global.debug "Setting region to" (r : Type.sexp_identifier_region_node)]);
      (* Handle children *)
      if not (young_region.mem type_)
      then (
        [%log.global.debug "Type not in young region" (id : Identifier.t)];
        (* [type_] is in parent or sibling regions *)
        ())
      else (
        [%log.global.debug "Type in young region, visiting children" (id : Identifier.t)];
        (* [type_] is in current region *)
        Type.structure type_ |> S.iter ~f:(fun type_ -> loop type_ r)))
  in
  young_region.region.types
  |> List.sort
       ~compare:(Comparable.lift Tree.Level.compare ~f:(Type.level_exn ~here:[%here]))
  |> List.iter ~f:(fun type_ -> loop type_ (Type.region_exn ~here:[%here] type_))
;;

let update_type_guards (young_region : Young_region.t) =
  [%log.global.debug "Updating type guards" (young_region : Young_region.t)];
  let visited = Hash_set.create (module Identifier) in
  (* INVARIANT: [parent_guards # parent_removed_guards] *)
  let rec loop type_ parent_guards parent_removed_guards =
    let structure = Type.structure type_ in
    let id = structure.id in
    let guards = structure.guards in
    let removed_guards = structure.removed_guards in
    if
      (* Previously visited *)
      Hash_set.mem visited id
      (* and no changes to be made *)
      && Guard.Map.is_subset parent_guards ~of_:guards
      && Set.are_disjoint parent_removed_guards (Guard.Map.key_set guards)
      && Set.is_empty removed_guards
    then ()
    else (
      [%log.global.debug "Visiting" (type_ : Type.t) (parent_guards : Type.t Guard.Map.t)];
      Hash_set.add visited id;
      let parent_guards = Guard.Map.remove_many parent_guards removed_guards in
      (* [parent_guards # parent_removed_guards union removed_guards] *)
      let guards = Guard.Map.remove_many guards parent_removed_guards in
      (* [guards # parent_removed_guards union removed_guards] *)
      let guards = Guard.Map.merge_skewed guards parent_guards in
      let removed_guards = Set.union parent_removed_guards removed_guards in
      Type.set_guards type_ guards;
      if young_region.mem type_
      then (
        [%log.global.debug "Type in young region, visiting children"];
        Type.set_removed_guards type_ Guard.Packed.Set.empty;
        S.Inner.iter structure.inner ~f:(fun type_ -> loop type_ guards removed_guards))
      else
        (* Set guards to remove (for later) *)
        Type.set_removed_guards type_ removed_guards)
  in
  young_region.region.types
  |> List.iter ~f:(fun type_ ->
    loop type_ (Type.guards type_) (Type.removed_guards type_))
;;

exception Rigid_variable_escape of (Range.t * Type.t)

let scope_check_young_region (young_region : Young_region.t) =
  [%log.global.debug "Scope check young region" (young_region : Young_region.t)];
  (* Iterate over rigid variables, if the level of the rigid variable is
     less than the young region level, then the rigid variable has escaped
     it's scope *)
  let young_level = young_region.node.level in
  let { Region.rigid_vars; raise_scope_escape; _ } = young_region.region in
  match
    List.find rigid_vars ~f:(fun var ->
      Tree.Level.(Type.level_exn ~here:[%here] var < young_level))
  with
  | None -> ()
  | Some var -> raise_scope_escape var
;;

let generalize_young_region ~state (young_region : Young_region.t) =
  [%log.global.debug "Generalizing young region" (young_region : Young_region.t)];
  assert (
    (* Cannot generalize fully generalized regions *)
    match young_region.region.status with
    | Fully_generalized -> false
    | _ -> true);
  let young_level = young_region.node.level in
  (* Generalize the region *)
  let propagate_work_list = Queue.create () in
  let generics =
    young_region.region.types
    |> List.filter ~f:(fun type_ ->
      Type.is_representative type_
      &&
      ([%log.global.debug "Visiting type" (type_ : Type.t)];
       let r = Type.region_exn ~here:[%here] type_ in
       [%log.global.debug "Region of type_" (r : Type.sexp_identifier_region_node)];
       if Tree.Level.(r.level < young_level)
       then (
         [%log.global.debug "Type is not generic"];
         (* Register [type_] in the region [r] *)
         visit_region ~state r;
         Region.(register_type (Tree.region r) type_);
         (* If the type is partial, we notify the instances and unify them with
            the ungeneralized partial type. *)
         Type.partial_ungeneralize type_ ~f:(fun instance_id instance ->
           let curr_region = Type.region_exn ~here:[%here] instance in
           visit_region ~state curr_region;
           unify ~state ~curr_region type_ instance;
           Type.remove_guard instance (Instance instance_id));
         (* Filter the type from the result list *)
         false)
       else (
         [%log.global.debug "Type is generic"];
         assert (Tree.Level.(r.level = young_level));
         (* If the type is a partial instance and has instances, then we propagate
            the structure. *)
         (match Type.status type_ with
          | Partial { kind = Instance; instances; _ } when not (Map.is_empty instances) ->
            Queue.enqueue propagate_work_list type_
          | _ -> ());
         (* Make the type generic *)
         Type.generalize type_;
         true)))
  in
  [%log.global.debug "Generics for young region" (generics : Type.t list)];
  (* Generalizing a rigid variable flexizes it. We remove the variable
     from [young_region.region.rigid_vars] to avoid unnecessary checks *)
  [%log.global.debug "Remove rigid vars from young region"];
  young_region.region.rigid_vars
  <- List.filter young_region.region.rigid_vars ~f:(fun type_ ->
       not (Type.is_generic type_));
  (* Propagate structures to partial instances *)
  [%log.global.debug "Propagating structure to partial instances"];
  Queue.iter propagate_work_list ~f:(fun partial_generic ->
    match Type.status partial_generic with
    | Instance _ | Partial { kind = Instance; _ } | Generic -> assert false
    | Partial { instances; kind = Generic; _ } ->
      Map.iteri instances ~f:(fun ~key:instance_id ~data:instance ->
        [%log.global.debug
          "Visiting instance of partial generic"
            (partial_generic : Type.t)
            (instance_id : Instance_identifier.t)
            (instance : Type.t)];
        (* The partial generic that links to [instance] has been fully generalized :) *)
        let curr_region = Type.region_exn ~here:[%here] instance in
        visit_region ~state curr_region;
        (* Perform a partial copy on the generic to ensure the instance has the generalized
           structure and then unify *)
        let copy = partial_copy ~state ~curr_region ~instance_id partial_generic in
        unify ~state ~curr_region copy instance));
  (* Generalize partial generics that can be generalized to (full) generics *)
  [%log.global.debug "Generalising partial generics"];
  List.iter
    generics
    ~f:
      (Type.partial_generalize ~f:(fun instance_id instance ->
         (* The partial generic associated with the instance [(guard, instance)] has
            been fully generalized.*)
         (* Remove the guard *)
         visit_region ~state (Type.region_exn ~here:[%here] instance);
         Type.remove_guard instance (Instance instance_id)));
  [%log.global.debug "Changes" (generics : Type.t list)];
  (* Schedule default handlers *)
  let roots_and_guarded_partial_generics =
    List.filter generics ~f:(fun type_ ->
      let structure = Type.structure type_ in
      match structure.status, structure.inner with
      | _, Var (Empty_one_or_more_handlers _) ->
        (* Must contain handlers *)
        true
      | Partial _, _ ->
        (* Or be guarded by a match handler *)
        not (Guard.Map.Match.is_empty structure.guards)
      | _ -> false)
  in
  [%log.global.debug
    "Roots and guarded partial generics"
      (roots_and_guarded_partial_generics : Type.t list)];
  let guard_graph =
    Guard_graph.create ~level:young_level ~roots_and_guarded_partial_generics
  in
  let never_realized_types = Guard_graph.never_realized guard_graph in
  [%log.global.debug
    "Never realized types"
      (never_realized_types : Type.t list list)
      (List.length never_realized_types : int)];
  List.iter never_realized_types ~f:(fun cycle ->
    List.iter cycle ~f:(fun type_ ->
      match Type.inner type_ with
      | Var (Empty_one_or_more_handlers handlers) ->
        List.iter handlers ~f:(fun handler ->
          Scheduler.schedule state.scheduler handler.default)
      | _ -> assert false));
  (* Update the region to only contain the remaining partial generics *)
  let partial_generics, generics =
    List.partition_tf generics ~f:(fun type_ ->
      match Type.status type_ with
      | Instance _ | Partial { kind = Instance; _ } ->
        (* No instances are left in the region *)
        assert false
      | Partial { kind = Generic; _ } -> true
      | Generic -> false)
  in
  young_region.region.types <- partial_generics;
  [%log.global.debug "Generalized generics" (generics : Type.t list)];
  [%log.global.debug "Updated region" (young_region.region : Type.region)];
  (* Update region status *)
  if List.is_empty partial_generics
  then young_region.region.status <- Fully_generalized
  else young_region.region.status <- Partially_generalized
;;

let update_and_generalize_young_region ~state young_region =
  update_type_levels ~state young_region;
  update_type_guards young_region;
  scope_check_young_region young_region;
  generalize_young_region ~state young_region
;;

let update_and_generalize ~state (curr_region : Type.region_node) =
  [%log.global.debug
    "Begin generalization"
      (curr_region.id : Identifier.t)
      (state.generalization_tree : Generalization_tree.t)];
  assert (Scheduler.is_empty state.scheduler);
  let young_region = Young_region.of_region_node curr_region in
  update_and_generalize_young_region ~state young_region;
  [%log.global.debug "End generalization" (curr_region.id : Identifier.t)]
;;

let create_scheme root region_node : Type.t Scheme.t =
  { root; region_node = Some region_node }
;;

let force_generalization ~state region_node =
  Generalization_tree.generalize_region
    state.generalization_tree
    region_node
    ~f:(update_and_generalize ~state)
    ~finally:(fun () ->
      [%log.global.debug
        "End generalization, Running scheduler" (state.scheduler : Scheduler.t)];
      Scheduler.run state.scheduler;
      [%log.global.debug
        "End generalization, Finished running scheduler" (state.scheduler : Scheduler.t)]);
  [%log.global.debug
    "Finished (forced) generalization" (region_node : Type.sexp_identifier_region_node)]
;;

let exit_region ~curr_region root = create_scheme root curr_region

let instantiate ~state ~curr_region ({ root; region_node } : Type.t Scheme.t) =
  [%log.global.debug
    "Generalization tree @ instantiation"
      (state.generalization_tree : Generalization_tree.t)];
  (* Generalize the region (if necessary) *)
  Option.iter region_node ~f:(force_generalization ~state);
  (* Create an instance group *)
  let instance_id = Instance_identifier.create state.id_source in
  (* Copy the type (always copy if possible) *)
  copy ~state ~curr_region ~when_:(Fn.const true) ~instance_id root
;;

module Suspended_match = struct
  type t =
    { matchee : Type.t
    ; closure : closure
    ; case : curr_region:Type.region_node -> Type.t R.t -> unit
    ; else_ : curr_region:Type.region_node -> unit
    }
  [@@deriving sexp_of]

  and closure = { variables : Type.t list } [@@deriving sexp_of]

  let closure_add_guard { variables } ~guard ~data =
    List.iter variables ~f:(fun type_ -> Type.add_guard type_ ~guard ~data)
  ;;

  let closure_remove_guard { variables } guard =
    List.iter variables ~f:(fun type_ -> Type.remove_guard type_ guard)
  ;;

  let match_or_yield ~state ~curr_region { matchee; case; closure; else_ } =
    match Type.inner matchee with
    | Var _ ->
      let guard = Guard.Match (Match_identifier.create state.id_source) in
      let data = Guard.Map.Data.Match matchee in
      [%log.global.debug "Suspended match guard" (guard : Guard.Match.t Guard.t)];
      let curr_region_of_closure () =
        visit_region ~state curr_region;
        curr_region
      in
      Type.add_handler
        matchee
        { run =
            (fun s ->
              let curr_region = curr_region_of_closure () in
              (* Remove guard from closure *)
              closure_remove_guard closure guard;
              (* Solve case *)
              case ~curr_region s;
              [%log.global.debug
                "Generalization tree after solving case"
                  (state.generalization_tree : Generalization_tree.t)])
        ; default =
            (fun () ->
              let curr_region = curr_region_of_closure () in
              else_ ~curr_region;
              [%log.global.debug
                "Generalization tree running default handler"
                  (state.generalization_tree : Generalization_tree.t)])
        };
      (* Add guard to closure *)
      closure_add_guard closure ~guard ~data
    | Structure s ->
      (* Optimisation: Immediately solve the case *)
      case ~curr_region s
  ;;
end
