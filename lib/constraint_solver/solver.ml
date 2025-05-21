open! Import
module C = Constraint
module G = Generalization
module Type = G.Type
module State = G.State

module Error = struct
  type t =
    { it : desc
    ; range : Range.t option
    }

  and desc =
    | Unsatisfiable of Mlsus_error.t
    | Unbound_type_var of C.Type.Var.t
    | Unbound_var of C.Var.t
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
    ; expr_vars : G.Scheme.t C.Var.Map.t
    ; curr_region : G.Type.region_node
    ; range : Range.t option
    }
  [@@deriving sexp_of]

  let raise t err = Error.raise ~range:t.range err
  let with_range t ~range = { t with range = Some range }

  let empty ~range ~curr_region =
    { type_vars = C.Type.Var.Map.empty; expr_vars = C.Var.Map.empty; curr_region; range }
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

  let enter_region ~state t =
    { t with
      curr_region =
        G.enter_region ~state t.curr_region ~raise_scope_escape:(fun _type ->
          raise t @@ Rigid_variable_escape)
    }
  ;;

  let exit_region ~state:_ t root = G.exit_region ~curr_region:t.curr_region root

  let of_gclosure
        (gclosure : G.Suspended_match.closure)
        ~closure:({ type_vars; vars } : C.Closure.t)
        ~range
        ~curr_region
    =
    let type_vars =
      List.zip_exn type_vars gclosure.variables |> C.Type.Var.Map.of_alist_exn
    in
    let expr_vars = List.zip_exn vars gclosure.schemes |> C.Var.Map.of_alist_exn in
    { (empty ~range ~curr_region) with type_vars; expr_vars }
  ;;

  let prev_region t =
    match t.curr_region.parent with
    | None -> t.curr_region
    | Some parent -> parent
  ;;
end

let rec gtype_of_type : state:State.t -> env:Env.t -> C.Type.t -> G.Type.t =
  fun ~state ~env type_ ->
  let self = gtype_of_type ~state ~env in
  match type_ with
  | Var type_var -> Env.find_type_var env type_var
  | App (type1, type2) ->
    G.create_former ~state ~curr_region:env.curr_region (App (self type1, self type2))
  | Spine types ->
    G.create_former ~state ~curr_region:env.curr_region (Spine (List.map types ~f:self))
  | Head hd -> G.create_former ~state ~curr_region:env.curr_region (Head hd)
;;

let match_type : state:State.t -> env:Env.t -> G.Type.t G.R.t -> Env.t * C.Type.Matchee.t =
  fun ~state ~env former ->
  let match_types ~env gtypes =
    List.fold_map gtypes ~init:env ~f:(fun env gtype ->
      let type_var = C.Type.Var.create ~id_source:state.id_source () in
      Env.bind_type_var env ~var:type_var ~type_:gtype, type_var)
  in
  match former with
  | Rigid_var -> env, Rigid_var
  | Structure (Spine gtypes) ->
    let env, type_vars = match_types ~env gtypes in
    env, Spine type_vars
  | Structure (App (gtype1, gtype2)) ->
    let type_var1 = C.Type.Var.create ~id_source:state.id_source () in
    let type_var2 = C.Type.Var.create ~id_source:state.id_source () in
    let env =
      env
      |> Env.bind_type_var ~var:type_var1 ~type_:gtype1
      |> Env.bind_type_var ~var:type_var2 ~type_:gtype2
    in
    env, App (type_var1, type_var2)
  | Structure (Head hd) -> env, Head hd
;;

let forall ~(state : State.t) ~env ~type_var =
  Env.bind_type_var
    env
    ~var:type_var
    ~type_:(G.create_rigid_var ~state ~curr_region:env.curr_region ())
;;

let exists ~(state : State.t) ~env ~type_var =
  Env.bind_type_var
    env
    ~var:type_var
    ~type_:(G.create_var ~state ~curr_region:env.curr_region ())
;;

let unify ~(state : State.t) ~(env : Env.t) gtype1 gtype2 =
  [%log.global.debug
    "Unify" (state : State.t) (env : Env.t) (gtype1 : Type.t) (gtype2 : Type.t)];
  try
    G.unify ~state ~curr_region:env.curr_region gtype1 gtype2;
    [%log.global.debug "(Unify) Running scheduler" (state.scheduler : G.Scheduler.t)];
    G.Scheduler.run state.scheduler
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
    [%log.global.debug "Binding var to scheme" (var : C.Var.t) (gscheme : G.Scheme.t)];
    let env = Env.bind_var env ~var ~type_:gscheme in
    [%log.global.debug "Solving let body"];
    self ~state ~env in_
  | Instance (var, expected_type) ->
    [%log.global.debug "Decoding expected_type" (expected_type : C.Type.t)];
    let expected_gtype = gtype_of_type ~state ~env expected_type in
    [%log.global.debug "Decoded expected_type" (expected_gtype : Type.t)];
    let var_gscheme = Env.find_var env var in
    [%log.global.debug "Instantiating scheme" (var : C.Var.t) (var_gscheme : G.Scheme.t)];
    let actual_gtype = G.instantiate ~state ~curr_region:env.curr_region var_gscheme in
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
      ~state
      ~curr_region:env.curr_region
      { matchee; closure = gclosure; case; else_ }
  | With_range (t, range) -> solve ~state ~env:(Env.with_range env ~range) t

and gclosure_of_closure ~env closure : G.Suspended_match.closure =
  let variables = List.map closure.type_vars ~f:(Env.find_type_var env) in
  let schemes = List.map closure.vars ~f:(Env.find_var env) in
  { variables; schemes }

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
  [%log.global.debug "Exiting region" (scheme : G.Scheme.t)];
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
    G.force_generalization ~state env.curr_region;
    [%log.global.debug "Generalized root region" (env.curr_region : Type.region_node)];
    [%log.global.debug "End state" (state : State.t)];
    (* No more regions to generalize *)
    assert (G.Generalization_tree.is_empty state.generalization_tree);
    (* No partial regions are left *)
    let num_partially_generalized_regions =
      G.Generalization_tree.num_partially_generalized_regions state.generalization_tree
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
