open! Import
module F = Structure.Former

module Region = struct
  (** The [Generalization] module manages the generalisation of graphical types.

      Each type belongs to a 'region', which indicates where those types are
      existentially bound in the solver's stack. *)
  type 'a t =
    { mutable status : status
    ; mutable types : 'a list
    }
  [@@deriving sexp_of]

  and status =
    | Not_generalized (** A region that is yet to be generalized *)
    | Partially_generalized (** A region that is 'partially' generalized *)
    | Fully_generalized (** A region that is ('fully') generalized *)
  [@@deriving sexp_of]

  let create () = { types = []; status = Not_generalized }
  let register_type t type_ = t.types <- type_ :: t.types

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

module Guard = Identifier

module Partial_status = struct
  type 'a t =
    { region_node : 'a Region.Tree.sexp_identifier_node
    ; instances : (Guard.t * 'a) list
    ; kind : kind
    }
  [@@deriving sexp_of]

  and kind =
    | Instance
    | Generic
  [@@deriving sexp_of]

  let merge_kind k1 k2 =
    match k1, k2 with
    | Instance, _ | _, Instance -> Instance
    | Generic, Generic -> Generic
  ;;

  let merge t1 t2 =
    { region_node = Tree.nearest_common_ancestor t1.region_node t2.region_node
    ; instances = t1.instances @ t2.instances
    ; kind = merge_kind t1.kind t2.kind
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

  let merge t1 t2 ~partial_unify =
    match t1, t2 with
    | Generic, _ | _, Generic -> assert false
    | Partial p1, Partial p2 -> Partial (Partial_status.merge p1 p2)
    | Partial { region_node = rn1; instances; kind = _ }, Instance rn2 ->
      List.iter instances ~f:partial_unify;
      Instance (Tree.nearest_common_ancestor rn1 rn2)
    | Instance rn1, Partial { region_node = rn2; instances; kind = _ } ->
      List.iter instances ~f:partial_unify;
      Instance (Tree.nearest_common_ancestor rn1 rn2)
    | Instance rn1, Instance rn2 -> Instance (Tree.nearest_common_ancestor rn1 rn2)
  ;;

  let of_region_node region_node =
    match (Region.Tree.region region_node).status with
    | Not_generalized -> Instance region_node
    | Partially_generalized -> Partial { region_node; instances = []; kind = Instance }
    | Fully_generalized -> assert false
  ;;
end

module S = struct
  module Inner = Structure.Suspended_first_order (F)

  type 'a t =
    { id : Identifier.t
    ; inner : 'a Inner.t
    ; guards : Guard.Set.t
    ; status : 'a Status.t
    }
  [@@deriving sexp_of]

  let create ~id_source ~region_node ?(guards = Guard.Set.empty) inner =
    { id = Identifier.create id_source
    ; status = Status.of_region_node region_node
    ; guards
    ; inner
    }
  ;;

  let generalize t =
    let if_guarded ~and_ ~then_ ~else_ =
      let status = if not (Set.is_empty t.guards && and_) then then_ else else_ in
      { t with status }
    in
    match t.status with
    | Generic -> assert false
    | Partial { kind = Generic; _ } ->
      (* [generalize] cannot generalize partial generics. See [partial_generalize] *)
      t
    | Partial ({ kind = Instance; instances; _ } as p) ->
      (* [generalize] cannot generalize partial generics *or* partial instances
         that have instances. *)
      if_guarded
        ~and_:(List.is_empty instances)
        ~then_:(Partial { p with kind = Generic })
        ~else_:Generic
    | Instance region_node ->
      if_guarded
        ~and_:true
        ~then_:(Partial { region_node; instances = []; kind = Generic })
        ~else_:Generic
  ;;

  let partial_generalize t ~f =
    match t.status with
    | Partial { kind = Generic; instances; region_node = _ } when Set.is_empty t.guards ->
      List.iter instances ~f;
      { t with status = Generic }
    | _ -> t
  ;;

  type 'a ctx =
    { id_source : Identifier.source
    ; curr_region : 'a Region.Tree.node
    ; schedule_remove_guard : 'a -> Guard.t -> unit
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
    let partial_unify (guard, inst) =
      (* It doesn't matter which type ([type1] or [type2]) we pick, since after
         the current unification is successful, [type1] and [type2] will refer to
         the *same* type. *)
      unify type2 inst;
      ctx.schedule_remove_guard inst guard
    in
    let status = Status.merge t1.status t2.status ~partial_unify in
    let inner =
      Inner.merge ~ctx:ctx.super ~create ~unify ~type1 ~type2 t1.inner t2.inner
    in
    let guards = Set.union t1.guards t2.guards in
    { id = t1.id; status; inner; guards }
  ;;

  let add_guard t guard = { t with guards = Set.add t.guards guard }
  let add_guards t guards = { t with guards = Set.union t.guards guards }
  let remove_guard t guard = { t with guards = Set.remove t.guards guard }
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

  let guards t = (structure t).guards

  let add_guard t guard =
    let structure = structure t in
    set_structure t (S.add_guard structure guard)
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
end

module Suspended_match = struct
  type t =
    { matchee : Type.t
    ; closure : closure
    ; case : curr_region:Type.region_node -> Type.t Structure.Former.t -> unit
    ; else_ : unit -> Mlsus_error.t
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

  (** [num_partially_generalized_regions t] returns the number of regions
      (previously visited and generalized) with the status [Partially_generalized]. *)
  val num_partially_generalized_regions : t -> int

  val cancel_partially_generalized_regions : t -> Mlsus_error.t list
end = struct
  type t =
    { entered_map : (Identifier.t, (Identifier.t, Type.region_node) Hashtbl.t) Hashtbl.t
      (** Maps node identifiers to immediate entered descendants *)
    ; partially_generalized_regions : (Identifier.t, Type.region_node) Hashtbl.t
      (** Tracks the partially generalized regions. If there are remaining
        partially generalized regions after generalizing the root region, it implies
        there exists suspended matches that were never scheduled (e.g. a cycle between matches). *)
    }
  [@@deriving sexp_of]

  let incr_partially_generalized_regions t (rn : Type.region_node) =
    Hashtbl.set t.partially_generalized_regions ~key:rn.id ~data:rn
  ;;

  let decr_partially_generalized_regions t (rn : Type.region_node) =
    Hashtbl.remove t.partially_generalized_regions rn.id
  ;;

  let num_partially_generalized_regions t = Hashtbl.length t.partially_generalized_regions

  let cancel_partially_generalized_regions t =
    (* Not particularly efficient, but only called in the case of errors *)
    Hashtbl.fold
      t.partially_generalized_regions
      ~init:[]
      ~f:(fun ~key:_ ~data:region_node acc ->
        let types = (Region.Tree.region region_node).types in
        List.fold types ~init:acc ~f:(fun acc type_ ->
          match Type.inner type_ with
          | Var (Empty_one_or_more_handlers handlers) ->
            acc @ List.map handlers ~f:(fun handler -> handler.cancel ())
          | _ -> acc))
  ;;

  let create () =
    { entered_map = Hashtbl.create (module Identifier)
    ; partially_generalized_regions = Hashtbl.create (module Identifier)
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

  let generalize_region t rn ~f ~finally =
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
           incr_partially_generalized_regions t rn
         | Partially_generalized, Fully_generalized ->
           [%log.global.debug
             "Was an partially generalized region, now is fully generalized"];
           decr_partially_generalized_regions t rn
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
    visit rn
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

open State

let visit_region ~state rn = Generalization_tree.visit_region state.generalization_tree rn

let root_region ~state =
  let rn = Tree.create ~id_source:state.id_source (Region.create ()) |> Tree.root in
  visit_region ~state rn;
  rn
;;

let enter_region ~state curr_region =
  let rn =
    Tree.create_node ~id_source:state.id_source ~parent:curr_region (Region.create ())
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

let create_former ~state ~curr_region ?guards former =
  create_type ~state ~curr_region ?guards (Structure former)
;;

let partial_copy ~state ~curr_region type_ =
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
           | _ -> false
         in
         if should_copy_structure
         then Type.set_inner copy (S.Inner.copy structure.inner ~f:loop);
         copy)
  in
  loop ~root:true type_
;;

exception Cannot_resume_suspended_generic of Mlsus_error.t list

let remove_guard ~state t guard =
  let visited = Hash_set.create (module Identifier) in
  let rec loop t =
    [%log.global.debug "Removing guard" (guard : Identifier.t) (t : Type.t)];
    let structure = Type.structure t in
    let id = structure.id in
    if Hash_set.mem visited id
    then assert (not (Set.mem structure.guards guard))
    else (
      Hash_set.add visited id;
      if Set.mem structure.guards guard
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
    let guard = Identifier.create state.id_source in
    [%log.global.debug "Suspended match guard" (guard : Guard.t)];
    Type.add_handler
      matchee
      { run =
          (fun s ->
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
            (* Solve case *)
            case ~curr_region s;
            (* Remove guards for each variable in closure *)
            List.iter closure.variables ~f:(fun type_ -> remove_guard ~state type_ guard);
            [%log.global.debug
              "Generalization tree after solving case"
                (state.generalization_tree : Generalization_tree.t)])
      ; cancel = else_
      };
    (* Add guards for each variable in closure *)
    List.iter closure.variables ~f:(fun type_ -> Type.add_guard type_ guard)
  | Structure s ->
    (* Optimisation: Immediately solve the case *)
    case ~curr_region s
;;

let unify ~state ~curr_region type1 type2 =
  let schedule_handler s (handler : _ S.Inner.Var.handler) =
    Scheduler.schedule state.scheduler (fun () -> handler.run s)
  in
  let schedule_remove_guard inst guard =
    Scheduler.schedule state.scheduler (fun () -> remove_guard ~state inst guard)
  in
  let unifier_ctx : _ S.ctx =
    { id_source = state.id_source
    ; curr_region
    ; super = { schedule_handler; super = () }
    ; schedule_remove_guard
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
        (guards : Guard.Set.t)
        (r : Type.sexp_identifier_region_node)];
    assert (Tree.Path.mem young_region.path r);
    let r' = Type.region_exn ~here:[%here] type_ in
    [%log.global.debug "Region of type_" (r' : Type.sexp_identifier_region_node)];
    assert (Tree.Path.mem young_region.path r');
    let id = Type.id type_ in
    if Hash_set.mem visited id
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
        (* Safety: [visit_region ~state rn] only updates an ancestor of
           [young_region] in the generalization tree

           [r'.level] must be at most [young_region.level].
           Given [r.level < r'.level], it follows that [r < young_region.level].
           Hence [r] must be an ancestor of [young_region] *)
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
        let guards = Set.union guards (Type.guards type_) in
        (* [type_] is in current region *)
        Type.structure type_ |> S.iter ~f:(fun type_ -> loop type_ guards r)))
  in
  young_region.region.types
  |> List.sort
       ~compare:(Comparable.lift Tree.Level.compare ~f:(Type.level_exn ~here:[%here]))
  |> List.iter ~f:(fun type_ ->
    loop type_ (Type.guards type_) (Type.region_exn ~here:[%here] type_))
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
         (* Safety: [visit_region ~state rn] only updates an ancestor of
            [young_region] in the generalization tree

            Since [r.level < young_region.level] *)
         visit_region ~state r;
         Region.(register_type (Tree.region r) type_);
         (* Filter the type from the result list *)
         false)
       else (
         [%log.global.debug "Type is generic"];
         assert (Tree.Level.(r.level = young_level));
         (* Make the type generic *)
         Type.generalize type_;
         (* Cannot generalize unresolved svar *)
         (match Type.status type_, Type.inner type_ with
          | Generic, Var (Empty_one_or_more_handlers handlers) ->
            raise
              (Cannot_resume_suspended_generic
                 (List.map handlers ~f:(fun handler -> handler.cancel ())))
          | _ -> ());
         true)))
  in
  [%log.global.debug "Generics for young region" (generics : Type.t list)];
  (* Propagate structures to partial instances *)
  [%log.global.debug "Propagating structure to partial instances"];
  List.iter generics ~f:(fun generic ->
    match Type.status generic with
    | Instance _ | Partial { kind = Instance; _ } ->
      (* No instances are left in the region *)
      assert false
    | Generic ->
      (* Ignore, nothing to do *)
      ()
    | Partial { instances; kind = Generic; _ } ->
      List.iter instances ~f:(fun (guard, instance) ->
        [%log.global.debug
          "Visiting instance of partial generic"
            (generic : Type.t)
            (guard : Guard.t)
            (instance : Type.t)];
        (* The partial generic that links to [instance] has been fully generalized :) *)
        let curr_region = Type.region_exn ~here:[%here] instance in
        (* Safety: [visit_region ~state rn] only updates an ancestor / sibling /
           descendant of sibling of [young_region] in the generalization tree.

           [instance] cannot be created in a descendant of [young_region] (due to scoping).
           Only in a sibling / a descendant of a sibling. *)
        visit_region ~state curr_region;
        (* Perform a partial copy on the generic to ensure the instance has the generalized
           structure and then unify *)
        let copy = partial_copy ~state ~curr_region generic in
        (* NOTE: Scheduler jobs that are queued by [unify] and [remove_guard] only visit siblings or parents. *)
        unify ~state ~curr_region copy instance));
  (* Generalize partial generics that can be generalized to (full) generics *)
  [%log.global.debug "Generalising partial generics"];
  List.iter
    generics
    ~f:
      (Type.partial_generalize ~f:(fun (guard, instance) ->
         (* The partial generic associated with the instance [(guard, instance)] has
            been fully generalized.*)
         (* Remove the guard *)
         remove_guard ~state instance guard));
  [%log.global.debug "Changes" (generics : Type.t list)];
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
        "End generalization, Finished running scheduler" (state.scheduler : Scheduler.t)])
;;

let exit_region ~curr_region root = create_scheme root curr_region

let partial_instantiate ~state ~curr_region type_ =
  let structure = Type.structure type_ in
  match structure.status with
  | Partial { kind = Generic; instances; region_node } ->
    (* HACK: Should be a fresh identifier, but its likely we can *share*
       guard ids (making things more efficient) *)
    let guard = structure.id in
    let copy = create_var ~state ~curr_region ~guards:(Guard.Set.singleton guard) () in
    (* Register the instance on the type we're instantiating *)
    Type.set_structure
      type_
      { structure with
        status =
          Partial { kind = Generic; region_node; instances = (guard, copy) :: instances }
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
  let rec loop type_ =
    let structure = Type.structure type_ in
    match structure.status with
    | Instance _ -> type_
    | _ ->
      (try Hashtbl.find_exn copies structure.id with
       | Not_found_s _ ->
         let copy = partial_instantiate ~state ~curr_region type_ in
         Hashtbl.set copies ~key:structure.id ~data:copy;
         Type.set_inner copy (S.Inner.copy ~f:loop structure.inner);
         copy)
  in
  loop root
;;
