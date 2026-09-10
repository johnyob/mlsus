open! Import
open Omniml_log
module G = Generalization
module S = Suspended

module State = struct
  type t =
    { gstate : G.State.t
    ; sstate : S.State.t
    ; scheduler : Scheduler.t
    ; mutable error_on_default : bool
    ; mutable suspended_match_errors : Omniml_error.t list
    }
  [@@deriving sexp_of]

  let create options =
    { gstate =
        G.State.create
          ~recursive_types:(Omniml_options.is_enabled options Recursive_types)
    ; sstate = S.State.create ()
    ; scheduler = Scheduler.create ()
    ; error_on_default = not (Omniml_options.is_enabled options Defaulting)
    ; suspended_match_errors = []
    }
  ;;

  let disable_defaulting t = t.error_on_default <- true
end

module Elaboration = struct
  type 'a t = Decoded_type.Decoder.t -> 'a

  let run t = t (Decoded_type.Decoder.create ())
  let return value _decoder = value
  let map t ~f decoder = f (t decoder)
  let decode type_ decoder = decoder type_

  let both t1 t2 decoder =
    let value1 = t1 decoder in
    let value2 = t2 decoder in
    value1, value2
  ;;
end

module Error = struct
  type t =
    { it : desc
    ; range : Range.t option
    }

  and desc =
    | Unsatisfiable of Omniml_error.t
    | Unbound_type_var of Type.Var.t
    | Unbound_var of Constraint.Var.t
    | Rigid_variable_escape
    | Cannot_unify of Decoded_type.t * Decoded_type.t
    | Cannot_discharge_match_constraints of Omniml_error.t list
    | Cycle of Decoded_type.t
  [@@deriving sexp]

  exception T of t

  let create ~range it = { it; range }
  let raise ~range it = raise @@ T { it; range }
end

module Env = struct
  type t =
    { type_vars : G.Type.t Type.Var.Map.t
    ; expr_vars : G.Scheme.t Constraint.Var.Map.t
    ; curr_region : G.Region.t
    ; range : Range.t option
    }
  [@@deriving sexp_of]

  let raise t err = Error.raise ~range:t.range err
  let with_range t ~range = { t with range = Some range }

  let empty ~range ~curr_region =
    { type_vars = Type.Var.Map.empty
    ; expr_vars = Constraint.Var.Map.empty
    ; curr_region
    ; range
    }
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

  let enter_new_region ~(state : State.t) t =
    { t with curr_region = G.new_region ~state:state.gstate ?range:t.range t.curr_region }
  ;;

  let create_scheme t root = G.create_scheme ~curr_region:t.curr_region root

  let of_sclosure
        (gclosure : S.Closure.t)
        ~closure:({ type_vars; vars } : Constraint.Closure.t)
        ~range
        ~curr_region
    =
    let type_vars = List.zip_exn type_vars gclosure.types |> Type.Var.Map.of_alist_exn in
    let expr_vars =
      List.zip_exn vars gclosure.schemes |> Constraint.Var.Map.of_alist_exn
    in
    { (empty ~range ~curr_region) with type_vars; expr_vars }
  ;;

  let prev_region t =
    match G.Region.parent t.curr_region with
    | None -> t.curr_region
    | Some parent -> parent
  ;;
end

let rec gtype_of_type : state:State.t -> env:Env.t -> Type.t -> G.Type.t =
  fun ~state ~env type_ ->
  let self = gtype_of_type ~state ~env in
  let gformer ~(env : Env.t) args shape =
    let curr_region = env.curr_region in
    G.create_former ~state:state.gstate ~curr_region { args; shape }
  in
  match type_ with
  | Var type_var -> Env.find_type_var env type_var
  | Arrow (t1, t2) -> gformer ~env [ self t1; self t2 ] Sh_arrow
  | Tuple ts -> gformer ~env (List.map ~f:self ts) (Sh_tuple (List.length ts))
  | Constr (ts, ident) ->
    gformer ~env (List.map ~f:self ts) (Sh_constr (List.length ts, ident))
  | Shape (ts, shape) -> gformer ~env (List.map ~f:self ts) shape
  | Scheme scheme ->
    let ts, scheme_shape = Principal_shape.scheme_shape_decomposition scheme in
    gformer ~env (List.map ~f:self ts) (Sh_scheme scheme_shape)
  | Poly scheme ->
    let ts, scheme_shape = Principal_shape.scheme_shape_decomposition scheme in
    gformer ~env (List.map ~f:self ts) (Sh_poly scheme_shape)
;;

let unify ~(state : State.t) ~(env : Env.t) gtype1 gtype2 =
  [%log.global.debug
    "Unify" (state : State.t) (env : Env.t) (gtype1 : G.Type.t) (gtype2 : G.Type.t)];
  try
    G.unify
      ~state:state.gstate
      ~scheduler:state.scheduler
      ~curr_region:env.curr_region
      gtype1
      gtype2;
    [%log.global.debug
      "(Unify) Running scheduler"
        (gtype1 : G.Type.t)
        (gtype2 : G.Type.t)
        (state.scheduler : Scheduler.t)];
    Scheduler.run state.scheduler
  with
  | G.Unify (gtype1, gtype2) ->
    let decoder = Decoded_type.Decoder.create () in
    (* The let bindings here are to used to ensure order.
       The first type will have the 'newest' allocated variables *)
    let dtype1 = decoder gtype1 in
    let dtype2 = decoder gtype2 in
    Env.raise env (Cannot_unify (dtype1, dtype2))
;;

let forall ~(state : State.t) ~env ~type_var =
  Env.bind_type_var
    env
    ~var:type_var
    ~type_:(G.create_rigid_var ~state:state.gstate ~curr_region:env.curr_region ())
;;

let forall_many ~state ~env type_vars =
  List.fold type_vars ~init:env ~f:(fun env type_var -> forall ~state ~env ~type_var)
;;

let exists ~(state : State.t) ~env ~type_var =
  Env.bind_type_var
    env
    ~var:type_var
    ~type_:(G.create_var ~state:state.gstate ~curr_region:env.curr_region ())
;;

let match_type
  : env:Env.t -> shape:Principal_shape.t -> args:G.Type.t list -> Env.t * Type.Matchee.t
  =
  fun ~env ~shape ~args ->
  let shape_quantifiers = Principal_shape.quantifiers shape in
  let env =
    List.fold2_exn shape_quantifiers args ~init:env ~f:(fun env quantifier arg ->
      Env.bind_type_var env ~var:quantifier ~type_:arg)
  in
  match shape with
  | Sh_arrow ->
    (match shape_quantifiers with
     | [ var1; var2 ] -> env, Arrow (var1, var2)
     | _ -> assert false)
  | Sh_tuple _n -> env, Tuple shape_quantifiers
  | Sh_constr (_n, ident) -> env, Constr (shape_quantifiers, ident)
  | Sh_scheme scheme_shape -> env, Scheme scheme_shape.scheme
  | Sh_poly scheme_shape -> env, Poly scheme_shape.scheme
;;

let rec solve : type a. state:State.t -> env:Env.t -> a Constraint.t -> a Elaboration.t =
  fun ~state ~env cst ->
  Global.Span.with_
    ~level:`Debug
    ~fields:(fun () ->
      [ "state", [%sexp (state : State.t)]
      ; "env", [%sexp (env : Env.t)]
      ; "constraint", [%sexp (cst : Constraint.t)]
      ])
    "solve"
    ~f:(fun () -> solve_body ~state ~env cst)

and solve_body : type a. state:State.t -> env:Env.t -> a Constraint.t -> a Elaboration.t =
  fun ~state ~env cst ->
  let self ~state ?(env = env) cst = solve ~state ~env cst in
  match cst with
  | True -> Elaboration.return ()
  | Return value -> Elaboration.return value
  | False err -> Env.raise env @@ Unsatisfiable err
  | Map (cst, f) -> Elaboration.map (self ~state cst) ~f
  | Conj (cst1, cst2) ->
    [%log.global.debug "Solving conj lhs"];
    let value1 = self ~state cst1 in
    [%log.global.debug "Solving conj rhs"];
    let value2 = self ~state cst2 in
    Elaboration.both value1 value2
  | Eq (type1, type2) ->
    [%log.global.debug "Decoding type1" (type1 : Type.t)];
    let gtype1 = gtype_of_type ~state ~env type1 in
    [%log.global.debug "Decoded type1" (gtype1 : G.Type.t)];
    [%log.global.debug "Decoding type2" (type2 : Type.t)];
    let gtype2 = gtype_of_type ~state ~env type2 in
    [%log.global.debug "Decoded type2" (gtype2 : G.Type.t)];
    unify ~state ~env gtype1 gtype2;
    Elaboration.return ()
  | Let (let_binding, in_) ->
    [%log.global.debug "Solving let binding"];
    let bound_value, gbindings = solve_let_binding ~state ~env let_binding in
    let env =
      List.fold gbindings ~init:env ~f:(fun env (var, gscheme) ->
        Env.bind_var env ~var ~type_:gscheme)
    in
    [%log.global.debug "Solving let body"];
    let body_value = self ~state ~env in_ in
    Elaboration.both bound_value body_value
  | Instance (var, expected_type) ->
    [%log.global.debug "Decoding expected_type" (expected_type : Type.t)];
    let expected_gtype = gtype_of_type ~state ~env expected_type in
    [%log.global.debug "Decoded expected_type" (expected_gtype : G.Type.t)];
    let var_gscheme = Env.find_var env var in
    [%log.global.debug
      "Instantiating scheme" (var : Constraint.Var.t) (var_gscheme : G.Scheme.t)];
    let actual_gtype =
      G.instantiate
        ~state:state.gstate
        ~scheduler:state.scheduler
        ~curr_region:env.curr_region
        var_gscheme
    in
    [%log.global.debug
      "Scheme instance" (var_gscheme : G.Scheme.t) (actual_gtype : G.Type.t)];
    unify ~state ~env actual_gtype expected_gtype;
    Elaboration.return ()
  | Decode type_ ->
    let gtype = gtype_of_type ~state ~env type_ in
    Elaboration.decode gtype
  | Exists (type_var, cst) ->
    [%log.global.debug "Binding unification for type_var" (type_var : Type.Var.t)];
    let env = exists ~state ~env ~type_var in
    [%log.global.debug "Updated env" (env : Env.t)];
    [%log.global.debug "Solving exist body"];
    self ~state ~env cst
  | Forall (type_vars, in_) ->
    let env = Env.enter_new_region ~state env in
    let env = forall_many ~state ~env type_vars in
    self ~state ~env in_
  | Match { matchee; closure; case; default; error } ->
    let gmatchee = Env.find_type_var env matchee in
    [%log.global.debug "Matchee type" (gmatchee : G.Type.t)];
    let sclosure = sclosure_of_closure ~env closure in
    let curr_region = env.curr_region in
    let env_of_sclosure () =
      let env = Env.of_sclosure sclosure ~closure ~curr_region ~range:env.range in
      let env = Env.bind_type_var env ~var:matchee ~type_:gmatchee in
      env
    in
    [%log.global.debug "Closure of suspended match" (sclosure : S.Closure.t)];
    (* Register match for the shape *)
    let with_ ~shape ~args =
      [%log.global.debug "Entered match handler" (shape : Principal_shape.t)];
      (* Enter region and construct env *)
      let env = env_of_sclosure () in
      [%log.global.debug "Handler env" (env : Env.t)];
      [%log.global.debug "Handler state" (state : State.t)];
      (* Solve *)
      let env, matchee = match_type ~env ~shape ~args in
      [%log.global.debug
        "Matchee and updated env" (matchee : Type.Matchee.t) (env : Env.t)];
      let cst = case matchee in
      [%log.global.debug "Generated constraint from case" (cst : Constraint.t)];
      ignore (solve ~state ~env cst : unit Elaboration.t);
      [%log.global.debug "Solved generated constraint" (cst : Constraint.t)];
      [%log.global.debug "Exiting case region"]
    in
    let default () =
      if state.error_on_default
      then state.suspended_match_errors <- error () :: state.suspended_match_errors
      else (
        match default () with
        | Shape shape ->
          let args =
            S.get_or_alloc_shape_args
              ~gstate:state.gstate
              ~scheduler:state.scheduler
              ~curr_region
              ~shape
              gmatchee
          in
          with_ ~shape ~args
        | Constraint cst ->
          let env = env_of_sclosure () in
          ignore (solve ~state ~env cst : unit Elaboration.t))
    in
    [%log.global.debug "Suspending match..."];
    S.match_
      ~state:state.sstate
      ~gstate:state.gstate
      ~scheduler:state.scheduler
      ~curr_region
      gmatchee
      ~with_
      ~closure:sclosure
      ~default;
    Elaboration.return ()
  | With_range (t, range) -> self ~state ~env:(Env.with_range env ~range) t

and solve_let_binding
  : type a.
    state:State.t
    -> env:Env.t
    -> a Constraint.let_binding
    -> a Elaboration.t * (Constraint.Var.t * G.Scheme.t) list
  =
  fun ~state ~env { type_vars; in_; bindings } ->
  let env = Env.enter_new_region ~state env in
  [%log.global.debug "Entered new region" (env : Env.t)];
  let env =
    List.fold type_vars ~init:env ~f:(fun env (flex, type_var) ->
      match flex with
      | Flexible -> exists ~state ~env ~type_var
      | Rigid -> forall ~state ~env ~type_var)
  in
  [%log.global.debug
    "Bound type vars"
      (type_vars : (Constraint.flexibility * Type.Var.t) list)
      (env : Env.t)];
  [%log.global.debug "Solving scheme's constraint"];
  let value = solve ~state ~env in_ in
  let gbindings =
    List.map bindings ~f:(fun { binding_var; binding_type } ->
      [%log.global.debug
        "Decoding binding type" (binding_var : Constraint.Var.t) (binding_type : Type.t)];
      let binding_gtype = gtype_of_type ~state ~env binding_type in
      [%log.global.debug
        "Type of binding" (binding_var : Constraint.Var.t) (binding_gtype : G.Type.t)];
      let gscheme = Env.create_scheme env binding_gtype in
      binding_var, gscheme)
  in
  [%log.global.debug "Bindings" (gbindings : (Constraint.Var.t * G.Scheme.t) list)];
  value, gbindings

and sclosure_of_closure ~env closure : S.Closure.t =
  let types = List.map closure.type_vars ~f:(Env.find_type_var env) in
  let schemes = List.map closure.vars ~f:(Env.find_var env) in
  { types; schemes }
;;

let default_unary ~(state : State.t) =
  S.Defaulting.unary ~state:state.sstate ~gstate:state.gstate ~scheduler:state.scheduler
;;

let default_all ~(state : State.t) =
  S.Defaulting.cancel_all
    ~state:state.sstate
    ~gstate:state.gstate
    ~scheduler:state.scheduler
;;

let solve
  : type a.
    ?range:Range.t -> options:Omniml_options.t -> a Constraint.t -> (a, Error.t) result
  =
  fun ?range ~options cst ->
  try
    let state = State.create options in
    let root_region = G.State.root_region state.gstate in
    let env = Env.empty ~curr_region:root_region ~range in
    [%log.global.debug "Initial env and state" (state : State.t) (env : Env.t)];
    let value = solve ~state ~env cst in
    [%log.global.debug "State" (state : State.t)];
    [%log.global.debug "Generalizing root region" (env.curr_region : G.Region.t)];
    if Omniml_options.is_enabled options Defaulting
    then (
      default_unary ~state;
      State.disable_defaulting state;
      default_all ~state)
    else default_all ~state;
    [%log.global.debug "Generalized root region" (env.curr_region : G.Region.t)];
    if not (Scheduler.is_empty state.scheduler)
    then raise_bug_s ~here:[%here] [%message "Scheduler not flushed"];
    (* No more regions to generalize *)
    if not (G.State.is_quiescent state.gstate)
    then raise_bug_s ~here:[%here] [%message "Region tree is not empty" (state : State.t)];
    if not (List.is_empty state.suspended_match_errors)
    then
      Error.raise ~range:None
      @@ Cannot_discharge_match_constraints state.suspended_match_errors;
    Ok (Elaboration.run value)
  with
  (* Catch solver exceptions *)
  | G.Unify (gtype1, gtype2) ->
    let decoder = Decoded_type.Decoder.create () in
    (* The let bindings here are to used to ensure order.
       The first type will have the 'newest' allocated variables *)
    let dtype1 = decoder gtype1 in
    let dtype2 = decoder gtype2 in
    Error (Error.create ~range (Cannot_unify (dtype1, dtype2)))
  | G.Rigid_variable_escape (range, _type) ->
    Error (Error.create ~range Rigid_variable_escape)
  | G.Cycle (range, gtype) ->
    let decoder = Decoded_type.Decoder.create () in
    let dtype = decoder gtype in
    Error (Error.create ~range (Cycle dtype))
  | Error.T err -> Error err
;;
