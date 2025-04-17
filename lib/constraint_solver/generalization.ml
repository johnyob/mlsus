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
    type 'a path = 'a t Tree.Path.t [@@deriving sexp_of]
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
  type ('a, 'v) t =
    | Match : Match_identifier.t -> ('a, 'a) t
    | Instance : Instance_identifier.t -> ('a, unit) t
  [@@deriving sexp_of]

  type 'a packed = Packed : ('a, 'v) t -> 'a packed
  [@@deriving sexp_of] [@@ocaml.unboxed]

  module Map : sig
    type ('a, 'v) key := ('a, 'v) t
    type 'a t [@@deriving sexp_of]

    val empty : 'a t
    val singleton : ('a, 'v) key -> 'v -> 'a t
    val is_empty : 'a t -> bool
    val is_subset : 'a t -> of_:'a t -> bool
    val mem : 'a t -> ('a, _) key -> bool
    val add : 'a t -> key:('a, 'v) key -> data:'v -> 'a t
    val remove : 'a t -> ('a, _) key -> 'a t
    val merge : 'a t -> 'a t -> 'a t
    val iter_match : 'a t -> f:(key:Match_identifier.t -> data:'a -> unit) -> unit
  end = struct
    type ('a, 'v) key = ('a, 'v) t

    type 'a t =
      { match_map : 'a Match_identifier.Map.t
      ; inst_set : Instance_identifier.Set.t
      }

    let sexp_of_t _sexp_of_a t =
      [%sexp_of: Match_identifier.Set.t * Instance_identifier.Set.t]
        (Map.key_set t.match_map, t.inst_set)
    ;;

    let empty =
      { match_map = Match_identifier.Map.empty; inst_set = Instance_identifier.Set.empty }
    ;;

    let is_empty t = Map.is_empty t.match_map && Set.is_empty t.inst_set

    let is_subset t1 ~of_:t2 =
      Set.is_subset (Map.key_set t1.match_map) ~of_:(Map.key_set t2.match_map)
      && Set.is_subset t1.inst_set ~of_:t2.inst_set
    ;;

    let mem (type a v) (t : a t) (key : (a, v) key) =
      match key with
      | Match mid -> Map.mem t.match_map mid
      | Instance iid -> Set.mem t.inst_set iid
    ;;

    let add (type a v) (t : a t) ~(key : (a, v) key) ~(data : v) : a t =
      match key with
      | Match mid -> { t with match_map = Map.set t.match_map ~key:mid ~data }
      | Instance iid -> { t with inst_set = Set.add t.inst_set iid }
    ;;

    let remove (type a v) (t : a t) (key : (a, v) key) =
      match key with
      | Match mid -> { t with match_map = Map.remove t.match_map mid }
      | Instance iid -> { t with inst_set = Set.remove t.inst_set iid }
    ;;

    let singleton key data = add empty ~key ~data

    let merge t1 t2 =
      { match_map =
          Map.merge_skewed t1.match_map t2.match_map ~combine:(fun ~key:_ type1 _type2 ->
            type1)
      ; inst_set = Set.union t1.inst_set t2.inst_set
      }
    ;;

    let iter_match t ~f = Map.iteri t.match_map ~f
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
    | Instance rn1, Instance rn2 -> Instance (Tree.nearest_common_ancestor rn1 rn2)
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
    ; status : 'a Status.t
    }
  [@@deriving sexp_of]

  let create ~id_source ~region_node ?(guards = Guard.Map.empty) inner =
    { id = Identifier.create id_source
    ; status = Status.of_region_node region_node
    ; guards
    ; inner
    }
  ;;

  let flexize t =
    match t.inner with
    | Structure Rigid_var -> { t with inner = Var Empty }
    | _ -> t
  ;;

  let is_generalizable t =
    let has_handler =
      match t.inner with
      | Var (Empty_one_or_more_handlers _) -> true
      | _ -> false
    in
    Guard.Map.is_empty t.guards && not has_handler
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
    ; schedule_remove_instance_guard : 'a -> Instance_identifier.t -> unit
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
      ctx.schedule_remove_instance_guard inst instance_id
    in
    let status = Status.merge t1.status t2.status ~unify ~partial_unify in
    let inner =
      Inner.merge ~ctx:ctx.super ~create ~unify ~type1 ~type2 t1.inner t2.inner
    in
    let guards = Guard.Map.merge t1.guards t2.guards in
    { id = t1.id; status; inner; guards }
  ;;

  let is_generic t = Status.is_generic t.status

  let add_guard t ~guard ~data =
    { t with guards = Guard.Map.add t.guards ~key:guard ~data }
  ;;

  let add_guards t guards = { t with guards = Guard.Map.merge t.guards guards }
  let remove_guard t guard = { t with guards = Guard.Map.remove t.guards guard }
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
  type region_path = t Region.Tree.path [@@deriving sexp_of]
  type region = t Region.t [@@deriving sexp_of]
  type scheme = t Scheme.t [@@deriving sexp_of]
  type 'a guard = (t, 'a) Guard.t [@@deriving sexp_of]
  type packed_guard = t Guard.packed [@@deriving sexp_of]
  type guard_map = t Guard.Map.t [@@deriving sexp_of]

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
  let guards t = (structure t).guards

  let add_guard t ~guard ~data =
    let structure = structure t in
    set_structure t (S.add_guard structure ~guard ~data)
  ;;

  let add_guards t guards =
    let structure = structure t in
    set_structure t (S.add_guards structure guards)
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
end

module Suspended_match = struct
  type t =
    { matchee : Type.t
    ; closure : closure
    ; case : curr_region:Type.region_node -> Type.t R.t -> unit
    ; else_ : curr_region:Type.region_node -> unit
    }
  [@@deriving sexp_of]

  and closure = { variables : Type.t list } [@@deriving sexp_of]
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
  val create : unit -> t

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
    }
  [@@deriving sexp_of]

  let incr_partially_generalized_regions t =
    t.num_partially_generalized_regions <- t.num_partially_generalized_regions + 1
  ;;

  let decr_partially_generalized_regions t =
    t.num_partially_generalized_regions <- t.num_partially_generalized_regions - 1
  ;;

  let num_partially_generalized_regions t = t.num_partially_generalized_regions

  let create () =
    { entered_map = Hashtbl.create (module Identifier)
    ; num_partially_generalized_regions = 0
    }
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

  let visit_region t (rn : Type.region_node) =
    if not (Hashtbl.mem t.entered_map rn.id)
    then (
      (* Enter [rn] *)
      let imm_descendants = Hashtbl.create (module Identifier) in
      Hashtbl.set t.entered_map ~key:rn.id ~data:imm_descendants;
      match find_closest_entered_ancestor t rn with
      | None -> ()
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
    Hashtbl.remove t.entered_map rn.id;
    match find_closest_entered_ancestor t rn with
    | None -> ()
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

  let create () =
    { id_source = Identifier.create_source ()
    ; generalization_tree = Generalization_tree.create ()
    ; scheduler = Scheduler.create ()
    }
  ;;
end

module Unify = Type.Make_unify (S)

module Young_region = struct
  type t =
    { region : Type.region
    ; node : Type.region_node
    ; path : Type.region_path (** A path to the current region *)
    ; mem : Type.t -> bool
      (** Returns [true] if given type is a member of the current region *)
    }
  [@@deriving sexp_of]

  let of_region_node region_node =
    let path = Tree.Path.of_node region_node in
    let region = Region.Tree.region region_node in
    let mem =
      let set =
        Hash_set.of_list (module Identifier) (region.types |> List.map ~f:Type.id)
      in
      fun type_ -> Hash_set.mem set (Type.id type_)
    in
    { region; node = region_node; path; mem }
  ;;

  let min_region_node_by_level t r1 r2 =
    if Tree.Path.compare_node_by_level t.path r1 r2 < 0 then r1 else r2
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
        else Guard.Map.iter_match (Type.guards node) ~f:(fun ~key:_ ~data:succ -> f succ)
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

let root_region ~state =
  let rn =
    Tree.create
      ~id_source:state.id_source
      (Region.create
         ~raise_scope_escape:(fun _ ->
           (* The root region should *not* bind rigid variables *)
           assert false)
         ())
    |> Tree.root
  in
  visit_region ~state rn;
  rn
;;

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

let create_type ~state ~curr_region ?guards inner =
  let type_ =
    Type.create
      (S.create ~id_source:state.id_source ~region_node:curr_region ?guards inner)
  in
  Region.(register_type (Tree.region curr_region) type_);
  type_
;;

let create_var ~state ~curr_region ?guards () =
  create_type ~state ~curr_region ?guards (Var Empty)
;;

let create_rigid_var ~state ~curr_region ?guards () =
  let rigid_var = create_type ~state ~curr_region ?guards (Structure Rigid_var) in
  Region.(register_rigid_var (Tree.region curr_region) rigid_var);
  rigid_var
;;

let create_former ~state ~curr_region ?guards former =
  create_type ~state ~curr_region ?guards (Structure (Structure former))
;;

let partial_copy ~state ~curr_region ~instance_id type_ =
  (* Copy generics fully, partial generics are shallowly copied (only fresh vars) *)
  let copies = Hashtbl.create (module Identifier) in
  let rec loop ?(root = false) type_ =
    let structure = Type.structure type_ in
    match structure.status with
    | Instance _ | Partial { kind = Instance; _ } -> type_
    | Generic | Partial { kind = Generic; _ } ->
      let id = structure.id in
      (try Hashtbl.find_exn copies id with
       | Not_found_s _ ->
         let copy = create_var ~state ~curr_region () in
         Hashtbl.set copies ~key:id ~data:copy;
         let should_copy_structure =
           root
           ||
           match structure.status with
           | Generic -> true
           | Partial ({ kind = Generic; instances; region_node = _ } as ps)
             when not (Map.mem instances instance_id) ->
             Type.add_guard copy ~guard:(Instance instance_id) ~data:();
             Type.set_structure
               type_
               { structure with
                 status =
                   Partial
                     { ps with instances = Map.set instances ~key:instance_id ~data:copy }
               };
             true
           | _ -> false
         in
         if should_copy_structure
         then Type.set_inner copy (S.Inner.copy structure.inner ~f:loop);
         copy)
  in
  loop ~root:true type_
;;

exception Cannot_resume_suspended_generic of Mlsus_error.t list

let remove_guard (type a) ~state t (guard : a Type.guard) =
  let visited = Hash_set.create (module Identifier) in
  [%log.global.debug "Removing guard" (Packed guard : Type.packed_guard)];
  let rec loop t =
    [%log.global.debug "Visiting" (t : Type.t)];
    let structure = Type.structure t in
    let id = structure.id in
    if Hash_set.mem visited id
    then assert (not (Guard.Map.mem structure.guards guard))
    else (
      Hash_set.add visited id;
      if Guard.Map.mem structure.guards guard
      then (
        [%log.global.debug "Visiting children" (t : Type.t)];
        let region = Type.region_exn ~here:[%here] t in
        visit_region ~state region;
        Type.remove_guard t guard;
        S.iter structure ~f:loop))
  in
  loop t
;;

let suspend ~state ~curr_region ({ matchee; case; closure; else_ } : Suspended_match.t) =
  match Type.inner matchee with
  | Var _ ->
    let guard = Guard.Match (Match_identifier.create state.id_source) in
    [%log.global.debug "Suspended match guard" (guard : (Type.t, Type.t) Guard.t)];
    let curr_region_of_closure () =
      let curr_region =
        (* Safety: The list of region nodes are on a given path from
           the root.

           This is because [matchee] and [closure.variables] are in the
           same scope (when initially referenced), thus must be on a given
           path from the root. And since unification maintains the invariant:
           {v
              v1 in rn1 on path p1 && v2 in rn2 on path p2 
                => unify(v1, v2) in nearest_common_ancestor(rn1, rn2)
                   on path longest_common_path(p1, p2)
           v}
           We conclude that any type on a given path [p] must be on a
           sub-path of [p]. So it follows that all the nodes are still
           on a given path from the root when the [case] is scheduled.
           The path in particular is defined by [Tree.Path.of_node curr_region]. *)
        Tree.unsafe_max_by_level
          (Type.region_exn ~here:[%here] matchee
           :: List.map closure.variables ~f:(fun type_ ->
             Type.region_exn ~here:[%here] type_))
      in
      visit_region ~state curr_region;
      curr_region
    in
    Type.add_handler
      matchee
      { run =
          (fun s ->
            let curr_region = curr_region_of_closure () in
            (* Solve case *)
            case ~curr_region s;
            (* Remove guards for each variable in closure *)
            List.iter closure.variables ~f:(fun type_ -> remove_guard ~state type_ guard);
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
    (* Add guards for each variable in closure *)
    List.iter closure.variables ~f:(fun type_ ->
      Type.add_guard type_ ~guard ~data:matchee)
  | Structure s ->
    (* Optimisation: Immediately solve the case *)
    case ~curr_region s
;;

let unify ~state ~curr_region type1 type2 =
  let schedule_handler s (handler : _ S.Inner.Var.handler) =
    Scheduler.schedule state.scheduler (fun () -> handler.run s)
  in
  let schedule_remove_instance_guard inst instance_id =
    Scheduler.schedule state.scheduler (fun () ->
      remove_guard ~state inst (Instance instance_id))
  in
  let unifier_ctx : _ S.ctx =
    { id_source = state.id_source
    ; curr_region
    ; super = { schedule_handler; super = () }
    ; schedule_remove_instance_guard
    }
  in
  Unify.unify ~ctx:unifier_ctx type1 type2
;;

let update_types ~state (young_region : Young_region.t) =
  [%log.global.debug "Updating types" (young_region : Young_region.t)];
  let visited = Hash_set.create (module Identifier) in
  let rec loop type_ guards r =
    (* Invariant: [r.level <= young_region.level] *)
    [%log.global.debug
      "Visiting"
        (type_ : Type.t)
        (guards : Type.t Guard.Map.t)
        (r : Type.sexp_identifier_region_node)];
    assert (Tree.Path.mem young_region.path r);
    let r' = Type.region_exn ~here:[%here] type_ in
    [%log.global.debug "Region of type_" (r' : Type.sexp_identifier_region_node)];
    assert (Tree.Path.mem young_region.path r');
    let id = Type.id type_ in
    if Hash_set.mem visited id && Guard.Map.is_subset guards ~of_:(Type.guards type_)
    then (
      [%log.global.debug "Already visited" (id : Identifier.t)];
      assert (Tree.Level.(r'.level <= r.level)))
    else (
      [%log.global.debug "Not previously visited" (id : Identifier.t)];
      Hash_set.add visited id;
      Type.add_guards type_ guards;
      [%log.global.debug "Marked as visited and added guards"];
      (* Visiting and updating region *)
      if Tree.Path.compare_node_by_level young_region.path r r' < 0
      then (
        visit_region ~state r;
        Type.set_region type_ r;
        [%log.global.debug "Setting region to" (r : Type.sexp_identifier_region_node)]);
      (* Handle children *)
      if not (young_region.mem type_)
      then (
        [%log.global.debug "Type not in young region" (id : Identifier.t)];
        (* [type_] is in parent regions *)
        assert (Tree.Level.(r'.level < young_region.node.level)))
      else (
        [%log.global.debug "Type in young region, visiting children" (id : Identifier.t)];
        let guards = Guard.Map.merge guards (Type.guards type_) in
        (* [type_] is in current region *)
        Type.structure type_ |> S.iter ~f:(fun type_ -> loop type_ guards r)))
  in
  young_region.region.types
  |> List.sort
       ~compare:(Comparable.lift Tree.Level.compare ~f:(Type.level_exn ~here:[%here]))
  |> List.iter ~f:(fun type_ ->
    loop type_ (Type.guards type_) (Type.region_exn ~here:[%here] type_))
;;

exception Rigid_variable_escape of (Range.t * Type.t)

let scope_check_young_region ~state:_ (young_region : Young_region.t) =
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
           remove_guard ~state instance (Instance instance_id));
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
        (* NOTE: Scheduler jobs that are queued by [unify] and [remove_guard] only visit siblings or parents. *)
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
         remove_guard ~state instance (Instance instance_id)));
  [%log.global.debug "Changes" (generics : Type.t list)];
  (* Schedule default handlers *)
  let roots_and_guarded_partial_generics =
    List.filter generics ~f:(fun type_ ->
      let structure = Type.structure type_ in
      match structure.status, structure.inner with
      | _, Var (Empty_one_or_more_handlers _) -> true
      | Partial _, _ -> not (Guard.Map.is_empty structure.guards)
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
  update_types ~state young_region;
  scope_check_young_region ~state young_region;
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

let partial_instantiate ~state ~curr_region ~instance_id type_ =
  let structure = Type.structure type_ in
  match structure.status with
  | Partial { kind = Generic; instances; region_node } ->
    let copy =
      create_var
        ~state
        ~curr_region
        ~guards:(Guard.Map.singleton (Instance instance_id) ())
        ()
    in
    (* Register the instance on the type we're instantiating *)
    Type.set_structure
      type_
      { structure with
        status =
          Partial
            { kind = Generic
            ; region_node
            ; instances = Map.set instances ~key:instance_id ~data:copy
            }
      };
    copy
  | Generic -> create_var ~state ~curr_region ()
  | Instance _ | Partial { kind = Instance; _ } ->
    (* Cannot instantiate instances *)
    assert false
;;

let instantiate ~state ~curr_region ({ root; region_node } : Type.t Scheme.t) =
  [%log.global.debug
    "Generalization tree @ instantiation"
      (state.generalization_tree : Generalization_tree.t)];
  (* Generalize the region (if necessary) *)
  Option.iter region_node ~f:(force_generalization ~state);
  (* Make the copy of the type *)
  let copies = Hashtbl.create (module Identifier) in
  let instance_id = Instance_identifier.create state.id_source in
  let rec loop type_ =
    let structure = Type.structure type_ in
    match structure.status with
    | Instance _ -> type_
    | _ ->
      (try Hashtbl.find_exn copies structure.id with
       | Not_found_s _ ->
         let copy = partial_instantiate ~state ~curr_region ~instance_id type_ in
         Hashtbl.set copies ~key:structure.id ~data:copy;
         Type.set_inner copy (S.Inner.copy ~f:loop structure.inner);
         copy)
  in
  loop root
;;
