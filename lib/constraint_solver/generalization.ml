open! Import
module F = Structure.Former
module R = Structure.Rigid (F)
module M = Structure.Shape_var (R)
module I = Structure.First_order (M)

module Pool = struct
  type 'node t =
    { mutable rigid_vars : 'node list
    ; range : Range.t option
    }
  [@@deriving sexp_of]

  let create ?range () = { rigid_vars = []; range }
  let register_rigid_var t rigid_var = t.rigid_vars <- rigid_var :: t.rigid_vars
end

module Instance_identifier = Identifier

module S = struct
  type 'node t =
    { inner : 'node I.t
    ; instances : 'node instances
    }

  and 'node instances = (int * 'node) Instance_identifier.Map.t [@@deriving sexp_of]

  type 'node ctx =
    { remove_guard : 'node -> unit
    ; prune_structure : 'node M.t -> 'node instances -> unit
    ; prune_instances : 'node -> unit
    ; scheduler : Scheduler.t
    }

  let super_ctx ctx : _ M.ctx =
    { scheduler = ctx.scheduler
    ; shape_of_structure =
        (function
          | Rigid_var -> None
          | Structure { shape; _ } -> Some shape)
    ; super = ()
    }
  ;;

  exception Cannot_merge = I.Cannot_merge

  let iter t ~f = I.iter t.inner ~f
  let is_var t = I.is_var t.inner

  let is_structurally_undetermined t =
    match t.inner with
    | Var | Structure (Shape_var _) -> true
    | Structure (Structure _) -> false
  ;;

  let merge ~ctx ~create ~unify ~type1 ~type2 t1 t2 =
    let create inner = create { inner; instances = Instance_identifier.Map.empty } in
    let inner =
      I.merge ~ctx:(super_ctx ctx) ~create ~unify ~type1 ~type2 t1.inner t2.inner
    in
    (match inner with
     | Structure (Shape_var _ as structure) ->
       (* Propagate a newly installed placeholder, but do not re-propagate when
          two existing placeholders are merged. *)
       if is_var t1 then ctx.prune_structure structure t1.instances;
       if is_var t2 then ctx.prune_structure structure t2.instances
     | Structure (Structure _ as structure) ->
       (* A concrete structure also refines an existing shape placeholder, so
          its instances must be updated just as they are for a plain variable. *)
       if is_structurally_undetermined t1 then ctx.prune_structure structure t1.instances;
       if is_structurally_undetermined t2 then ctx.prune_structure structure t2.instances
     | _ -> ());
    let instances =
      Map.merge_skewed
        t1.instances
        t2.instances
        ~combine:(fun ~key:_ (level1, inst1) (level2, inst2) ->
          assert (level1 = level2);
          (* Both edges belong to the same instance group. The second edge is
             redundant after their destinations have been unified. *)
          (* Invariant: inst2 is guaranteed to neither be [type1] nor [type2] *)
          ctx.remove_guard inst2;
          unify inst1 inst2;
          level1, inst1)
    in
    (* The generalizer may lower the instances. Once unification completes,
       we should prune instances. We only need to prune the instances of
       one of the types (since they're merged after unification) *)
    ctx.prune_instances type1;
    { inner; instances }
  ;;

  module Region_metadata = struct
    type 'node t = 'node Pool.t [@@deriving sexp_of]
  end
end

module G = Omniml_collector.Make (S)

module State = struct
  type t =
    { id_source : (Identifier.source[@sexp.opaque])
    ; type_state : G.State.t
    ; recursive_types : bool
    }
  [@@deriving sexp_of]

  let create ~recursive_types =
    let id_source = Identifier.create_source () in
    let root_pool = Pool.create () in
    let type_state = G.State.create ~id_source ~root:root_pool in
    { id_source; type_state; recursive_types }
  ;;

  let root_region t = G.State.root_region t.type_state
  let num_alive_regions t = G.State.num_alive_regions t.type_state
  let is_quiescent t = G.State.is_quiescent t.type_state
end

module Region = struct
  type t = G.Region.t [@@deriving sexp_of]

  let pool = G.Region.metadata
  let parent = G.Region.parent
  let level t = (G.Region.level t :> int)
  let register_rigid_var t rigid_var = Pool.register_rigid_var (pool t) rigid_var
end

module Type = struct
  type t = G.Node.t [@@deriving sexp_of]

  let structure = G.Node.structure
  let is_representative = G.Node.is_representative
  let same_class = G.Node.same_class
  let id = G.Node.id
  let region = G.Node.region
  let level t = Region.level (region t)
  let is_generic = G.Node.is_dead
  let is_var t = S.is_var (structure t)
  let inner t = (structure t).inner
  let instances t = (structure t).instances

  module Mark = struct
    type 'a t = (Identifier.t, 'a) Hashtbl.t [@@deriving sexp_of]

    let create () = Hashtbl.create (module Identifier)

    let mark t term data =
      match Hashtbl.add t ~key:(id term) ~data with
      | `Ok -> true
      | `Duplicate -> false
    ;;
  end

  let try_mark t mark data = Mark.mark mark t data

  let update_structure ~state t f =
    G.Node.update_structure ~state:state.State.type_state t ~f
  ;;

  let add_instance ~state t iid instance =
    update_structure ~state t (fun structure ->
      { structure with
        instances = Map.add_exn structure.instances ~key:iid ~data:instance
      })
  ;;

  let add_guard ~state t = G.Node.Rooting.root ~state:state.State.type_state t
  let remove_guard ~state t = G.Node.Rooting.unroot ~state:state.State.type_state t

  let create ~(state : State.t) ~curr_region inner =
    G.Node.create
      ~state:state.type_state
      ~curr_region
      { S.inner; instances = Instance_identifier.Map.empty }
  ;;

  module Unsafe = struct
    include G.Node.Unsafe

    let lower = promote
  end
end

exception Unify = G.Node.Unify

module Scheme = struct
  type t =
    { root : Type.t
    ; region : Region.t
    }
  [@@deriving sexp_of]

  let body t = t.root

  let iter_instances_and_partial_generics t ~f =
    let visited = Hash_set.create (module Identifier) in
    let rec loop type_ =
      let id = Type.id type_ in
      if not (Hash_set.mem visited id)
      then (
        Hash_set.add visited id;
        if Type.is_generic type_ then I.iter (Type.inner type_) ~f:loop else f type_)
    in
    loop t.root
  ;;
end

let create_var ~state ~curr_region () = Type.create ~state ~curr_region Var

let create_shape_var ~state ~curr_region ?shape () =
  Type.create
    ~state
    ~curr_region
    (Structure
       (Shape_var (Principal_shape.Var.create ~id_source:state.id_source ?shape ())))
;;

let create_rigid_var ~state ~curr_region () =
  let rigid_var = Type.create ~state ~curr_region (Structure (Structure Rigid_var)) in
  Region.register_rigid_var curr_region rigid_var;
  rigid_var
;;

let create_former ~state ~curr_region former =
  Type.create ~state ~curr_region (Structure (Structure (Structure former)))
;;

let flexize_inner = function
  | I.Structure (Structure Rigid_var) -> I.Var
  | inner -> inner
;;

let prune_instances ~(state : State.t) type_ ~unify_inst =
  let dst = Type.region type_ in
  let structure = Type.structure type_ in
  let instances =
    Map.filter structure.instances ~f:(fun (src_level, instance) ->
      if src_level > Region.level dst
      then (
        Type.remove_guard ~state instance;
        unify_inst type_ instance;
        false)
      else true)
  in
  (* Safety: prune_instances is called after unification (immediately after
     the dirty bit has been set) or by the generalizer.  *)
  Type.Unsafe.set_structure type_ { structure with instances }
;;

let rec prune_structure ~(state : State.t) ~scheduler structure instances =
  let inner = flexize_inner (Structure structure) in
  Map.iteri instances ~f:(fun ~key:instance_id ~data:(src_level, instance) ->
    let dst_region = Type.region instance in
    let copy =
      Type.create
        ~state
        ~curr_region:dst_region
        (I.map inner ~f:(copy ~state ~instance_id ~src_level ~dst_region))
    in
    unify ~state ~scheduler ~curr_region:dst_region copy instance)

and copy ~(state : State.t) type_ ~instance_id ~src_level ~dst_region =
  let generic_copies = Hashtbl.create (module Identifier) in
  let shape_var_copies = Hashtbl.create (module Identifier) in
  let rec visit type_ =
    if Type.level type_ < src_level
    then type_
    else if Type.is_generic type_
    then find_or_alloc_generic_copy type_
    else find_or_alloc_instance_copy type_
  and copy_shape_var shape_var =
    Hashtbl.find_or_add
      shape_var_copies
      (Principal_shape.Var.id shape_var)
      ~default:(fun () ->
        Principal_shape.Var.create
          ~id_source:state.id_source
          ?shape:(Principal_shape.Var.shape shape_var)
          ())
  and copy_inner type_ inner =
    match inner with
    | I.Structure (Shape_var shape_var) when Type.is_generic type_ ->
      I.Structure (Shape_var (copy_shape_var shape_var))
    | inner -> I.map inner ~f:visit
  and alloc_copy ~on_alloc type_ =
    let copy = create_var ~state ~curr_region:dst_region () in
    on_alloc copy;
    let inner = Type.inner type_ in
    let inner = if Type.is_generic type_ then inner else flexize_inner inner in
    let inner_copy = copy_inner type_ inner in
    unify_var
      ~state
      ~curr_region:dst_region
      copy
      (Type.create ~state ~curr_region:dst_region inner_copy);
    copy
  and find_or_alloc_generic_copy type_ =
    let id = Type.id type_ in
    Hashtbl.find_or_add generic_copies id ~default:(fun () ->
      alloc_copy
        ~on_alloc:(fun copy -> Hashtbl.set generic_copies ~key:id ~data:copy)
        type_)
  and find_or_alloc_instance_copy type_ =
    match Map.find (Type.instances type_) instance_id with
    | Some (instance_src_level, instance) ->
      assert (src_level = instance_src_level);
      instance
    | None ->
      alloc_copy
        ~on_alloc:(fun instance ->
          Type.add_guard ~state instance;
          Type.add_instance ~state type_ instance_id (src_level, instance))
        type_
  in
  visit type_

and unify ~(state : State.t) ~scheduler ~curr_region type1 type2 =
  let prune_instances_worklist = Queue.create () in
  let prune_structure_worklist = Queue.create () in
  let unify_inst_worklist = Queue.create () in
  let ctx : _ S.ctx =
    { remove_guard =
        (fun type_ ->
          (* Safety: we can mutate type_ directly here instead of queueing
             this operation since it is guaranteed not to overwrite the
             type currently being unified. *)
          Type.remove_guard ~state type_)
    ; scheduler
    ; prune_structure =
        (fun structure instances ->
          Queue.enqueue prune_structure_worklist (structure, instances))
    ; prune_instances =
        (fun type_ -> Queue.enqueue prune_instances_worklist (type_, Type.level type_))
    }
  in
  let unify type1 type2 =
    G.Node.try_unify_or_rollback ~state:state.type_state ~curr_region ~ctx type1 type2
  in
  unify type1 type2;
  let unify_inst type_ instance = Queue.enqueue unify_inst_worklist (type_, instance) in
  Queue.iter prune_instances_worklist ~f:(fun (type_, prev_level) ->
    (* Safety: LCA ensures that comparison by levels is safe here. *)
    if Type.level type_ < prev_level then prune_instances ~state type_ ~unify_inst);
  Queue.iter unify_inst_worklist ~f:(fun (type_, instance) -> unify type_ instance);
  Queue.iter prune_structure_worklist ~f:(fun (structure, instances) ->
    prune_structure ~state ~scheduler structure instances)

and unify_var ~state ~curr_region var type_ =
  assert (Type.is_var var);
  let dummy_scheduler = Scheduler.create () in
  unify ~state ~curr_region ~scheduler:dummy_scheduler var type_;
  assert (Scheduler.is_empty dummy_scheduler)
;;

let new_region ~(state : State.t) ?range curr_region =
  let pool = Pool.create ?range () in
  G.Region.create ~state:state.type_state ~parent:curr_region pool
;;

let create_scheme ~curr_region root : Scheme.t = { root; region = curr_region }

exception Rigid_variable_escape of Range.t option * Type.t

let rigid_scope_check region =
  let pool = Region.pool region in
  let region_level = Region.level region in
  match List.find pool.rigid_vars ~f:(fun var -> Type.level var < region_level) with
  | None -> ()
  | Some var -> raise (Rigid_variable_escape (pool.range, var))
;;

exception Cycle of Range.t option * Type.t

let occurs_check region =
  let region_level = Region.level region in
  (* The [visited_tbl] table records the types that are being visited 
     (mapped to [false]) and the types that have been visited 
     (mapped to [true]).  *)
  let visited_tbl : (Identifier.t, bool) Hashtbl.t = Hashtbl.create (module Identifier) in
  (* A cycle occurs when we reach a type that is mapped to [false]. *)
  let rec visit type_ =
    (* The occurs check solely looks for cycles in generalized types. *)
    if Type.level type_ = region_level
    then (
      let id = Type.id type_ in
      match Hashtbl.find_exn visited_tbl id with
      | visited -> if not visited then raise (Cycle ((Region.pool region).range, type_))
      | exception _ ->
        (* Mark this type as being visited *)
        Hashtbl.set visited_tbl ~key:id ~data:false;
        (* Visit its children *)
        I.iter (Type.inner type_) ~f:visit;
        (* Mark this type as visited *)
        Hashtbl.set visited_tbl ~key:id ~data:true)
  in
  G.Region.nodes region |> List.iter ~f:visit
;;

let before_generalize ~(state : State.t) region =
  rigid_scope_check region;
  if not state.recursive_types then occurs_check region
;;

let finalize ~state type_ =
  let structure = Type.structure type_ in
  Map.iter structure.instances ~f:(fun (_src_level, instance) ->
    Type.remove_guard ~state instance);
  (* Safety: the generalizer owns [type_] while running [finalize]. *)
  G.Node.Unsafe.set_structure
    type_
    { inner = flexize_inner structure.inner; instances = Instance_identifier.Map.empty }
;;

let promote ~state ~scheduler type_ =
  prune_instances ~state type_ ~unify_inst:(fun type_ instance ->
    Scheduler.enqueue scheduler (fun () ->
      unify ~state ~scheduler ~curr_region:(Type.region type_) type_ instance))
;;

let generalize_region ~(state : State.t) ~scheduler region =
  G.collect_region
    ~state:state.type_state
    ~before_mark:(fun () -> Scheduler.run scheduler)
    ~before_sweep:(before_generalize ~state)
    ~promote:(promote ~state ~scheduler)
    ~finalize:(finalize ~state)
    ~after_sweep:(fun () -> Scheduler.run scheduler)
    region
;;

let generalize_all_regions ~(state : State.t) ~scheduler () =
  G.collect_all_regions
    ~state:state.type_state
    ~before_mark:(fun () -> Scheduler.run scheduler)
    ~before_sweep:(before_generalize ~state)
    ~promote:(promote ~state ~scheduler)
    ~finalize:(finalize ~state)
    ~after_sweep:(fun () -> Scheduler.run scheduler)
    ()
;;

let instantiate ~state ~scheduler ~curr_region ({ root; region = src_region } : Scheme.t) =
  generalize_region ~state ~scheduler src_region;
  let instance_id = Instance_identifier.create state.State.id_source in
  copy
    ~state
    ~src_level:(Region.level src_region)
    ~dst_region:curr_region
    ~instance_id
    root
;;
