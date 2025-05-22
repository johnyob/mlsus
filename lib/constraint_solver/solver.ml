open! Import
module C = Constraint
module G = Generalization
module Type = G.Type
module Scheme_skeleton_ident = C.Type.Scheme_skeleton_ident

module Scheme_skeleton = struct
  type t =
    { closure : G.Type.t list
    ; scheme : G.Type.t G.Scheme.t
    }
  [@@deriving sexp_of]
end

module State = struct
  type t =
    { g : G.State.t
    ; defunc_scheme : Defunctionalized_scheme.State.t
    ; skeletons : Scheme_skeleton.t Scheme_skeleton_ident.Table.t
    }
  [@@deriving sexp_of]

  let id_source t = t.g.id_source

  let alloc_scheme_skeleton_ident t scheme_skeleton =
    let scheme_skeleton_ident =
      Scheme_skeleton_ident.create ~id_source:(id_source t) ()
    in
    Hashtbl.set t.skeletons ~key:scheme_skeleton_ident ~data:scheme_skeleton;
    scheme_skeleton_ident
  ;;

  let create_with_root_region () =
    let g, root_region = G.State.create_with_root_region () in
    ( { g
      ; defunc_scheme = Defunctionalized_scheme.State.create ()
      ; skeletons = Hashtbl.create (module Scheme_skeleton_ident)
      }
    , root_region )
  ;;
end

module Error = struct
  type t =
    { it : desc
    ; range : Range.t option
    }

  and desc =
    | Unsatisfiable of Mlsus_error.t
    | Unbound_type_var of C.Type.Var.t
    | Unbound_var of C.Var.t
    | Unknown_scheme_skeleton_ident of Scheme_skeleton_ident.t
    | Rigid_variable_escape
    | Cannot_unify of Decoded_type.t * Decoded_type.t
  [@@deriving sexp]

  exception T of t

  let create ~range it = { it; range }
  let raise ~range it = raise @@ T { it; range }
end

module Env = struct
  type t =
    { type_vars : Type.t C.Type.Var.Map.t
    ; expr_vars : Type.scheme C.Var.Map.t
    ; curr_region : G.Type.region_node
    ; range : Range.t option
    }
  [@@deriving sexp_of]

  let raise t err = Error.raise ~range:t.range err
  let with_range t ~range = { t with range = Some range }

  let empty ~range ~curr_region =
    let open C.Type in
    { type_vars = Var.Map.empty; expr_vars = C.Var.Map.empty; curr_region; range }
  ;;

  let bind_type_var t ~var ~type_ =
    { t with type_vars = Map.set t.type_vars ~key:var ~data:type_ }
  ;;

  let bind_var t ~var ~type_ =
    { t with expr_vars = Map.set t.expr_vars ~key:var ~data:type_ }
  ;;

  let find_type_var t type_var =
    try Map.find_exn t.type_vars type_var with
    | _ -> raise t @@ Unbound_type_var type_var
  ;;

  let find_var t expr_var =
    try Map.find_exn t.expr_vars expr_var with
    | _ -> raise t @@ Unbound_var expr_var
  ;;

  let enter_region ~(state : State.t) t =
    { t with
      curr_region =
        G.enter_region ~state:state.g t.curr_region ~raise_scope_escape:(fun _type ->
          raise t @@ Rigid_variable_escape)
    }
  ;;

  let exit_region ~state:(_ : State.t) t root =
    G.exit_region ~curr_region:t.curr_region root
  ;;

  let of_gclosure
        (gclosure : G.Suspended_match.closure)
        ~(closure : C.Closure.t)
        ~range
        ~curr_region
    =
    let type_vars =
      List.zip_exn closure.type_vars gclosure.variables |> C.Type.Var.Map.of_alist_exn
    in
    { (empty ~range ~curr_region) with type_vars }
  ;;

  let prev_region t =
    match t.curr_region.parent with
    | None -> t.curr_region
    | Some parent -> parent
  ;;
end

let forall ~(state : State.t) ~env ~type_var =
  Env.bind_type_var
    env
    ~var:type_var
    ~type_:(G.create_rigid_var ~state:state.g ~curr_region:env.curr_region ())
;;

let forall_many ~state ~env type_vars =
  List.fold type_vars ~init:env ~f:(fun env type_var -> forall ~state ~env ~type_var)
;;

let exists ~(state : State.t) ~env ~type_var =
  Env.bind_type_var
    env
    ~var:type_var
    ~type_:(G.create_var ~state:state.g ~curr_region:env.curr_region ())
;;

let exists_many ~state ~env type_vars =
  List.fold type_vars ~init:env ~f:(fun env type_var -> exists ~state ~env ~type_var)
;;

let rec gtype_of_type : state:State.t -> env:Env.t -> C.Type.t -> G.Type.t =
  fun ~state ~env type_ ->
  let self = gtype_of_type ~state ~env in
  let create_gtype = G.create_former ~state:state.g ~curr_region:env.curr_region in
  match type_ with
  | Var type_var -> Env.find_type_var env type_var
  | App (type1, type2) -> create_gtype (App (self type1, self type2))
  | Spine types -> create_gtype (Spine (List.map types ~f:self))
  | Head hd -> create_gtype (Head hd)
  | Defunctionalized_scheme scm ->
    let { Defunctionalized_scheme.closure; skeleton } =
      Defunctionalized_scheme.of_constraint_scheme
        scm
        ~state:state.defunc_scheme
        ~alloc_skeleton:(alloc_scheme_skeleton ~state ~env)
    in
    create_gtype
      (App
         ( create_gtype (Spine (List.map closure ~f:(Env.find_type_var env)))
         , create_gtype (Head (Scheme skeleton)) ))

and alloc_scheme_skeleton
  :  state:State.t
  -> env:Env.t
  -> closure:C.Type.Var.t list
  -> scheme:C.Type.scheme
  -> Scheme_skeleton_ident.t
  =
  fun ~state ~env ~closure ~scheme ->
  let gscheme_skeleton =
    gscheme_skeleton_of_scheme_skeleton ~state ~env ~closure ~scheme
  in
  State.alloc_scheme_skeleton_ident state gscheme_skeleton

and gscheme_skeleton_of_scheme_skeleton
  :  state:State.t
  -> env:Env.t
  -> closure:C.Type.Var.t list
  -> scheme:C.Type.scheme
  -> Scheme_skeleton.t
  =
  fun ~state ~env ~closure ~scheme ->
  let env = Env.enter_region ~state env in
  let env = exists_many ~state ~env closure in
  let env = exists_many ~state ~env scheme.scheme_quantifiers in
  let scm_root = gtype_of_type ~state ~env scheme.scheme_body in
  let closure = List.map closure ~f:(Env.find_type_var env) in
  let scheme = Env.exit_region ~state env scm_root in
  { Scheme_skeleton.closure; scheme }
;;

let find_scheme_skeleton
      ~(state : State.t)
      ~(env : Env.t)
      (scheme_skeleton_ident : Scheme_skeleton_ident.t)
  =
  try Hashtbl.find_exn state.skeletons scheme_skeleton_ident with
  | _ -> Env.raise env @@ Unknown_scheme_skeleton_ident scheme_skeleton_ident
;;

let match_type : state:State.t -> env:Env.t -> G.Type.t G.R.t -> Env.t * C.Type.Matchee.t =
  fun ~state ~env former ->
  let id_source = State.id_source state in
  let match_types ~env gtypes =
    List.fold_map gtypes ~init:env ~f:(fun env gtype ->
      let type_var = C.Type.Var.create ~id_source () in
      Env.bind_type_var env ~var:type_var ~type_:gtype, type_var)
  in
  match former with
  | Rigid_var -> env, Rigid_var
  | Structure (Spine gtypes) ->
    let env, type_vars = match_types ~env gtypes in
    env, Spine type_vars
  | Structure (App (gtype1, gtype2)) ->
    let type_var1 = C.Type.Var.create ~id_source () in
    let type_var2 = C.Type.Var.create ~id_source () in
    let env =
      env
      |> Env.bind_type_var ~var:type_var1 ~type_:gtype1
      |> Env.bind_type_var ~var:type_var2 ~type_:gtype2
    in
    env, App (type_var1, type_var2)
  | Structure (Head hd) -> env, Head hd
;;

let unify ~(state : State.t) ~(env : Env.t) gtype1 gtype2 =
  [%log.global.debug
    "Unify" (state : State.t) (env : Env.t) (gtype1 : Type.t) (gtype2 : Type.t)];
  let gstate = state.g in
  try
    G.unify ~state:gstate ~curr_region:env.curr_region gtype1 gtype2;
    [%log.global.debug "(Unify) Running scheduler" (gstate.scheduler : G.Scheduler.t)];
    G.Scheduler.run gstate.scheduler
  with
  | G.Unify.Unify (gtype1, gtype2) ->
    let decoder = Decoded_type.Decoder.create () in
    (* The let bindings here are to used to ensure order. 
       The first type will have the 'newest' allocated variables *)
    let dtype1 = decoder gtype1 in
    let dtype2 = decoder gtype2 in
    Env.raise env @@ Cannot_unify (dtype1, dtype2)
;;

let rec solve : state:State.t -> env:Env.t -> C.t -> unit =
  fun ~state ~env cst ->
  [%log.global.debug "Solving constraint" (state : State.t) (env : Env.t) (cst : C.t)];
  let self ~state ?(env = env) cst = solve ~state ~env cst in
  match cst with
  | True -> ()
  | False err -> Env.raise env @@ Unsatisfiable err
  | Conj (cst1, cst2) ->
    [%log.global.debug "Solving conj lhs"];
    self ~state cst1;
    [%log.global.debug "Solving conj rhs"];
    self ~state cst2
  | Eq (type1, type2) ->
    [%log.global.debug "Decoding type1" (type1 : C.Type.t)];
    let gtype1 = gtype_of_type ~state ~env type1 in
    [%log.global.debug "Decoded type1" (gtype1 : Type.t)];
    [%log.global.debug "Decoding type2" (type2 : C.Type.t)];
    let gtype2 = gtype_of_type ~state ~env type2 in
    [%log.global.debug "Decoded type2" (gtype2 : Type.t)];
    unify ~state ~env gtype1 gtype2
  | Let (var, scheme, in_) ->
    [%log.global.debug "Solving let scheme"];
    let gscheme = gscheme_of_scheme ~state ~env scheme in
    [%log.global.debug "Binding var to scheme" (var : C.Var.t) (gscheme : Type.scheme)];
    let env = Env.bind_var env ~var ~type_:gscheme in
    [%log.global.debug "Solving let body"];
    self ~state ~env in_
  | Instance (var, expected_type) ->
    [%log.global.debug "Decoding expected_type" (expected_type : C.Type.t)];
    let expected_gtype = gtype_of_type ~state ~env expected_type in
    [%log.global.debug "Decoded expected_type" (expected_gtype : Type.t)];
    let var_gscheme = Env.find_var env var in
    [%log.global.debug "Instantiating scheme" (var : C.Var.t) (var_gscheme : Type.scheme)];
    let _, actual_gtype =
      G.instantiate
        ~state:state.g
        ~curr_region:env.curr_region
        ~quantifiers:[]
        var_gscheme
    in
    [%log.global.debug "Scheme instance" (actual_gtype : Type.t)];
    unify ~state ~env actual_gtype expected_gtype
  | Exists (type_var, cst) ->
    [%log.global.debug "Binding unification for type_var" (type_var : C.Type.Var.t)];
    let env = exists ~state ~env ~type_var in
    [%log.global.debug "Updated env" (env : Env.t)];
    [%log.global.debug "Solving exist body"];
    self ~state ~env cst
  | Lower type_var ->
    let gtype = Env.find_type_var env type_var in
    [%log.global.debug "Type to be lowered" (gtype : Type.t)];
    let prev_region = Env.prev_region env in
    [%log.global.debug "Prev region" (prev_region : Type.sexp_identifier_region_node)];
    Type.set_region gtype prev_region
  | Match { matchee; closure; case = f; else_ } ->
    let matchee = Env.find_type_var env matchee in
    [%log.global.debug "Matchee type" (matchee : Type.t)];
    let gclosure = gclosure_of_closure ~env closure in
    [%log.global.debug
      "Closure of suspended match" (gclosure : G.Suspended_match.closure)];
    let case ~curr_region structure =
      [%log.global.debug "Entered match handler" (structure : Type.t G.R.t)];
      (* Enter region and construct env *)
      let env = Env.of_gclosure gclosure ~closure ~curr_region ~range:env.range in
      [%log.global.debug "Handler env" (env : Env.t)];
      [%log.global.debug "Handler state" (state : State.t)];
      (* Solve *)
      let env, matchee = match_type ~state ~env structure in
      [%log.global.debug
        "Matchee and updated env" (matchee : C.Type.Matchee.t) (env : Env.t)];
      let cst = f matchee in
      [%log.global.debug "Generated constraint from case" (cst : C.t)];
      solve ~state ~env cst;
      [%log.global.debug "Solved generated constraint" (cst : C.t)];
      [%log.global.debug "Exiting case region"]
    in
    let else_ ~curr_region =
      [%log.global.debug "Entered match default handler"];
      let env = Env.of_gclosure gclosure ~curr_region ~closure ~range:env.range in
      [%log.global.debug "Handler env" (env : Env.t)];
      [%log.global.debug "Handler state" (state : State.t)];
      let cst = else_ () in
      [%log.global.debug "Generated constraint from else" (cst : C.t)];
      solve ~state ~env cst;
      [%log.global.debug "Solved generated constraint" (cst : C.t)];
      [%log.global.debug "Exiting else region"]
    in
    [%log.global.debug "Suspending match..."];
    G.Suspended_match.match_or_yield
      ~state:state.g
      ~curr_region:env.curr_region
      { matchee; closure = gclosure; case; else_ }
  | With_range (t, range) -> solve ~state ~env:(Env.with_range env ~range) t
  | Instance_scheme (scm, type_) ->
    let scheme_skeleton = find_scheme_skeleton ~env ~state scm.scheme_skeleton in
    let expected_gtype = gtype_of_type ~state ~env type_ in
    let closure, actual_gtype =
      G.instantiate
        ~state:state.g
        ~curr_region:env.curr_region
        ~quantifiers:scheme_skeleton.closure
        scheme_skeleton.scheme
    in
    unify ~state ~env expected_gtype actual_gtype;
    let closure_spine =
      G.create_former ~state:state.g ~curr_region:env.curr_region (Spine closure)
    in
    unify ~state ~env closure_spine (gtype_of_type ~state ~env scm.scheme_closure)
  | Forall (type_vars, in_) ->
    (* No need to explicitly exit the region since lazily generalization will handle it :) *)
    let env = Env.enter_region ~state env in
    let env = forall_many ~state ~env type_vars in
    self ~state ~env in_

and gclosure_of_closure ~env closure : G.Suspended_match.closure =
  let variables = List.map closure.type_vars ~f:(Env.find_type_var env) in
  { variables }

and gscheme_of_scheme ~state ~env { type_vars; in_; type_ } =
  let env = Env.enter_region ~state env in
  [%log.global.debug "Entered new region" (env : Env.t)];
  let env =
    List.fold type_vars ~init:env ~f:(fun env (flex, type_var) ->
      match flex with
      | Flexible -> exists ~state ~env ~type_var
      | Rigid -> forall ~state ~env ~type_var)
  in
  [%log.global.debug
    "Bound type vars" (type_vars : (C.flexibility * C.Type.Var.t) list) (env : Env.t)];
  let type_ = gtype_of_type ~state ~env type_ in
  [%log.global.debug "Solving scheme's constraint"];
  solve ~state ~env in_;
  [%log.global.debug "Type of scheme" (type_ : Type.t)];
  let scheme = Env.exit_region ~state env type_ in
  [%log.global.debug "Exiting region" (scheme : Type.scheme)];
  scheme
;;

let solve : ?range:Range.t -> C.t -> (unit, Error.t) result =
  fun ?range cst ->
  try
    let state, root_region = State.create_with_root_region () in
    let env = Env.empty ~curr_region:root_region ~range in
    [%log.global.debug "Initial env and state" (state : State.t) (env : Env.t)];
    solve ~state ~env cst;
    [%log.global.debug "State" (state : State.t)];
    [%log.global.debug "Generalizing root region" (env.curr_region : Type.region_node)];
    G.force_generalization ~state:state.g env.curr_region;
    [%log.global.debug "Generalized root region" (env.curr_region : Type.region_node)];
    [%log.global.debug "End state" (state : State.t)];
    (* No more regions to generalize *)
    assert (G.Generalization_tree.is_empty state.g.generalization_tree);
    (* No partial regions are left *)
    let num_partially_generalized_regions =
      G.Generalization_tree.num_partially_generalized_regions state.g.generalization_tree
    in
    (if num_partially_generalized_regions > 0
     then
       Mlsus_error.(
         raise
         @@ bug_s
              ~here:[%here]
              [%message
                "There are still partially generalized regions"
                  (num_partially_generalized_regions : int)]));
    Ok ()
  with
  (* Catch solver exceptions *)
  | Error.T err -> Error err
;;
