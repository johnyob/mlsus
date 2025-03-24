open! Import
open Ast_types
open Ast
open Constraint

module Convert = struct
  let type_name ~env (type_name : Type_name.t) : (Adt.Type_ident.t * int) Or_error.t =
    let open Or_error.Let_syntax in
    let%map type_def =
      (* Disambiguate to the first type declaration *)
      Env.find_type_def env type_name
      |> List.hd
      |> Or_error.of_option
           ~error:
             (Error.create_s [%message "Unbound type name" (type_name : Type_name.t)])
    in
    type_def.type_ident, type_def.type_arity
  ;;

  module Core_type = struct
    let rec to_type_expr ~env (type_ : Ast.core_type) : Adt.type_expr Or_error.t =
      let open Adt in
      let open Or_error.Let_syntax in
      match type_ with
      | Type_var v -> return @@ Type_var v
      | Type_arrow (type1, type2) ->
        let%map type_expr1 = to_type_expr ~env type1
        and type_expr2 = to_type_expr ~env type2 in
        Type_arrow (type_expr1, type_expr2)
      | Type_tuple types ->
        let%map type_exprs = types |> List.map ~f:(to_type_expr ~env) |> Or_error.all in
        Type_tuple type_exprs
      | Type_constr (arg_types, constr) ->
        let%bind constr, expected_arity = type_name ~env constr in
        let actual_arity = List.length arg_types in
        if expected_arity <> actual_arity
        then
          error_s
            [%message
              "Type constructor arity mistmatch"
                (type_ : Ast.core_type)
                (expected_arity : int)
                (actual_arity : int)]
        else (
          let%map arg_types =
            arg_types |> List.map ~f:(to_type_expr ~env) |> Or_error.all
          in
          Type_constr (arg_types, constr))
    ;;

    let rec to_type ~env (type_ : Ast.core_type) : Type.t Or_error.t =
      let open Or_error.Let_syntax in
      match type_ with
      | Type_var v ->
        let%map v =
          Env.find_type_var env v
          |> Or_error.of_option
               ~error:
                 (Error.create_s [%message "Unbound type variable" (v : Type_var_name.t)])
        in
        Type.var v
      | Type_arrow (type1, type2) ->
        let%map type1 = to_type ~env type1
        and type2 = to_type ~env type2 in
        Type.(type1 @-> type2)
      | Type_tuple types ->
        let%map types = types |> List.map ~f:(to_type ~env) |> Or_error.all in
        Type.tuple types
      | Type_constr (arg_types, constr) ->
        let%bind constr, expected_arity = type_name ~env constr in
        let actual_arity = List.length arg_types in
        if expected_arity <> actual_arity
        then
          error_s
            [%message
              "Type constructor arity mistmatch"
                (type_ : Ast.core_type)
                (expected_arity : int)
                (actual_arity : int)]
        else (
          let%map arg_types = arg_types |> List.map ~f:(to_type ~env) |> Or_error.all in
          Type.constr arg_types constr)
    ;;
  end

  let rec type_expr ~env (type_ : Adt.type_expr) : Type.t Or_error.t =
    let open Or_error.Let_syntax in
    match type_ with
    | Type_var v ->
      let%map v =
        Env.find_type_var env v
        |> Or_error.of_option
             ~error:
               (Error.create_s [%message "Unbound type variable" (v : Type_var_name.t)])
      in
      Type.var v
    | Type_arrow (type_expr1, type_expr2) ->
      let%map type1 = type_expr ~env type_expr1
      and type2 = type_expr ~env type_expr2 in
      Type.(type1 @-> type2)
    | Type_tuple type_exprs ->
      let%map types = type_exprs |> List.map ~f:(type_expr ~env) |> Or_error.all in
      Type.tuple types
    | Type_constr (arg_type_exprs, constr) ->
      let%map arg_types =
        arg_type_exprs |> List.map ~f:(type_expr ~env) |> Or_error.all
      in
      Type.constr arg_types constr
  ;;

  let core_scheme ~(env : Env.t) ({ scheme_quantifiers; scheme_body } : Ast.core_scheme)
    : (Type.Var.t list * Type.t) Or_error.t
    =
    let open Or_error.Let_syntax in
    let env, quantifiers =
      List.fold_map scheme_quantifiers ~init:env ~f:(fun env type_var ->
        Env.rename_type_var env ~type_var ~in_:(fun env ctype_var -> env, ctype_var))
    in
    let%map body = Core_type.to_type ~env scheme_body in
    quantifiers, body
  ;;
end

let infer_constant const =
  match const with
  | Const_int _ -> Predef.int
  | Const_bool _ -> Predef.bool
  | Const_unit -> Predef.unit
;;

let infer_constructor_arity constr_arg : Adt.constructor_arity =
  match constr_arg with
  | None -> Zero
  | Some _ -> One
;;

let infer_constructor ~id_source constr_def constr_arg' constr_type' =
  let open Or_error.Let_syntax in
  let { Adt.constructor_alphas
      ; constructor_arg
      ; constructor_type
      ; constructor_name = _
      ; constructor_ident = _
      ; constructor_type_ident = _
      }
    =
    constr_def
  in
  (* Bind [alphas] existentially *)
  let env, constr_vars =
    List.fold_map
      constructor_alphas
      ~init:(Env.empty ~id_source ())
      ~f:(fun env type_var ->
        Env.rename_type_var env ~type_var ~in_:(fun env ctype_var -> env, ctype_var))
  in
  (* Convert [constructor_arg] and [constructor_type] *)
  let%bind c_constr_arg =
    match constr_arg', constructor_arg with
    | None, None -> return tt
    | Some constr_arg', Some constr_arg ->
      let%map constr_arg = Convert.type_expr ~env constr_arg in
      constr_arg' =~ constr_arg
    | Some _, None ->
      error_s [%message "Constructor has arity of zero, but argument was given"]
    | None, Some _ ->
      error_s [%message "Constructor has arity of one, but no argument was given"]
  in
  let%map constr_type = Convert.type_expr ~env constructor_type in
  exists_many constr_vars @@ (constr_type' =~ constr_type &~ c_constr_arg)
;;

let inst_constr
      ~(env : Env.t)
      ~constr_name
      ~(constr_arity : Adt.constructor_arity)
      ~constr_type
      k
  =
  let open Or_error.Let_syntax in
  let constr_arg_var = Type.Var.create ~id_source:(Env.id_source env) () in
  let constr_arg =
    match constr_arity with
    | Zero -> None
    | One -> Some (Type.var constr_arg_var)
  in
  let%bind c_type =
    (* Lookup constructor *)
    match Env.find_constr env constr_name with
    | [] -> error_s [%message "Unbound constructor" (constr_name : Constructor_name.t)]
    | [ constr_decl ] ->
      infer_constructor ~id_source:(Env.id_source env) constr_decl constr_arg constr_type
    | constr_defs ->
      (* Type-based disambiguation, filter the constructor definition in the environment with
         the type identifiers. *)
      let disambiguate_constr_defs_by_type_ident type_ident =
        let open Adt in
        match
          List.filter constr_defs ~f:(fun constr_def ->
            Type_ident.(constr_def.constructor_type_ident = type_ident))
        with
        | [ constr_def ] -> return constr_def
        | [] ->
          error_s
            [%message
              "No constructors with expected type ident"
                (constr_name : Constructor_name.t)
                (type_ident : Type_ident.t)]
        | constr_defs ->
          error_s
            [%message
              "Ambiguous constructors with expected type ident"
                (constr_name : Constructor_name.t)
                (constr_defs : constructor_definition list)
                (type_ident : Type_ident.t)]
      in
      let disambiguate_and_infer_constructor type_ident =
        let%bind constr_def = disambiguate_constr_defs_by_type_ident type_ident in
        infer_constructor ~id_source:(Env.id_source env) constr_def constr_arg constr_type
      in
      (match constr_type with
       | Var constr_type_var ->
         return
         @@ match_
              constr_type_var
              ~closure:[ constr_type_var; constr_arg_var ]
              ~with_:(function
              | (Arrow _ | Tuple _) as matchee ->
                ff
                  (Error.create_s
                     [%message
                       "Expected a constructor type, but got arrow/tuple"
                         (matchee : Type.Matchee.t)])
              | Constr (_, type_ident) ->
                (match disambiguate_and_infer_constructor type_ident with
                 | Ok cst -> cst
                 | Error err -> ff err))
       | Constr (_, type_ident) -> disambiguate_and_infer_constructor type_ident
       | Arrow _ | Tuple _ ->
         error_s [%message "Expected variable or constructor type" (constr_type : Type.t)])
  in
  let%bind result, c_arg = k constr_arg in
  return (result, exists constr_arg_var (c_arg &~ c_type))
;;

module Pattern = struct
  module Fragment = struct
    type t = { var_bindings : Type.t Var_name.Map.t } [@@deriving sexp_of]

    let empty = { var_bindings = Var_name.Map.empty }
    let singleton var type_ = { var_bindings = Var_name.Map.singleton var type_ }

    let extend t ~var ~type_ =
      { var_bindings = Map.set t.var_bindings ~key:var ~data:type_ }
    ;;

    let merge t1 t2 =
      { var_bindings =
          Map.merge_skewed t1.var_bindings t2.var_bindings ~combine:(fun ~key:_ _ b -> b)
      }
    ;;

    let to_alist t = Map.to_alist t.var_bindings
  end

  let exists' ~id_source f =
    let open Or_error.Let_syntax in
    let a = Type.Var.create ~id_source () in
    let%map result, c = f (Type.var a) in
    result, exists a c
  ;;

  let rec infer_pat ~env pat pat_type k =
    let open Or_error.Let_syntax in
    match pat with
    | Pat_any -> k (Fragment.empty, tt)
    | Pat_var x -> k (Fragment.singleton x pat_type, tt)
    | Pat_alias (pat, x) ->
      infer_pat ~env pat pat_type
      @@ fun (f, c) ->
      let f = Fragment.extend f ~var:x ~type_:pat_type in
      k (f, c)
    | Pat_const const -> k (Fragment.empty, pat_type =~ infer_constant const)
    | Pat_tuple pats ->
      infer_pats ~env pats
      @@ fun (f, pat_types, c) -> k (f, c &~ Type.(pat_type =~ tuple pat_types))
    | Pat_constr (constr, arg_pat) ->
      inst_constr
        ~env
        ~constr_name:constr
        ~constr_arity:(infer_constructor_arity arg_pat)
        ~constr_type:pat_type
      @@ fun arg_type ->
      (match arg_pat, arg_type with
       | Some arg_pat, Some arg_type -> infer_pat ~env arg_pat arg_type k
       | None, None -> k (Fragment.empty, tt)
       | _ ->
         Or_error.error_s
           [%message "Constructor argument mistmatch in pattern" (pat : Ast.pattern)])
    | Pat_annot (pat, annot) ->
      let%bind type_ = Convert.Core_type.to_type ~env annot in
      infer_pat ~env pat pat_type @@ fun (f, c) -> k (f, pat_type =~ type_ &~ c)

  and infer_pats ~env pats k =
    match pats with
    | [] -> k (Fragment.empty, [], tt)
    | pat :: pats ->
      exists' ~id_source:(Env.id_source env)
      @@ fun pat_type ->
      infer_pat ~env pat pat_type
      @@ fun (f, c1) ->
      infer_pats ~env pats
      @@ fun (f', pat_types, c2) ->
      k (Fragment.merge f f', pat_type :: pat_types, c1 &~ c2)
  ;;
end

module Expression = struct
  let exists' ~id_source f =
    let open Or_error.Let_syntax in
    let a = Type.Var.create ~id_source () in
    let%map c = f (Type.var a) in
    exists a c
  ;;

  let bind_pat ~env pat pat_type ~in_ =
    let open Or_error.Let_syntax in
    (Pattern.infer_pat ~env pat pat_type
     @@ fun (fragment, c) ->
     let env, bindings =
       fragment
       |> Pattern.Fragment.to_alist
       |> List.fold_map ~init:env ~f:(fun env (var, type_) ->
         Env.rename_var env ~var ~in_:(fun env cvar -> env, (cvar, type_)))
     in
     let%map in_ = in_ env in
     ( ()
     , c
       &~ List.fold bindings ~init:in_ ~f:(fun in_ (cvar, type_) ->
         let_ cvar#=(mono_scheme type_) ~in_) ))
    >>| snd
  ;;

  let rec infer_exp ~(env : Env.t) exp exp_type =
    let open Or_error.Let_syntax in
    let id_source = Env.id_source env in
    match exp with
    | Exp_var var ->
      let%bind var =
        Env.find_var env var
        |> Or_error.of_option
             ~error:(Error.create_s [%message "Unbound variable" (var : Var_name.t)])
      in
      return @@ inst var exp_type
    | Exp_const const -> return @@ (exp_type =~ infer_constant const)
    | Exp_fun (pat, exp) ->
      exists' ~id_source
      @@ fun a1 ->
      exists' ~id_source
      @@ fun a2 ->
      let%map c = bind_pat ~env pat a1 ~in_:(fun env -> infer_exp ~env exp a2) in
      Type.(exp_type =~ a1 @-> a2) &~ c
    | Exp_app (exp1, exp2) ->
      exists' ~id_source
      @@ fun a1 ->
      exists' ~id_source
      @@ fun a2 ->
      let%bind c1 = infer_exp ~env exp1 a2 in
      let%map c2 = infer_exp ~env exp2 a1 in
      Type.(a2 =~ a1 @-> exp_type) &~ c1 &~ c2
    | Exp_let (value_binding, exp) ->
      infer_value_binding ~env value_binding @@ fun env -> infer_exp ~env exp exp_type
    | Exp_exists (type_vars, exp) ->
      let env, type_vars =
        List.fold_map type_vars ~init:env ~f:(fun env type_var ->
          Env.rename_type_var env ~type_var ~in_:(fun env ctype_var -> env, ctype_var))
      in
      let%map c = infer_exp ~env exp exp_type in
      exists_many type_vars c
    | Exp_annot (exp, annot) ->
      let%bind annot = Convert.Core_type.to_type ~env annot in
      let%map c = infer_exp ~env exp exp_type in
      exp_type =~ annot &~ c
    | Exp_tuple exps ->
      infer_exps ~env exps
      @@ fun (exp_types, c) ->
      let%map c = c in
      Type.(exp_type =~ tuple exp_types) &~ c
    | Exp_if_then_else (if_exp, then_exp, else_exp) ->
      let%bind c1 = infer_exp ~env if_exp Predef.bool in
      let%bind c2 = infer_exp ~env then_exp exp_type in
      let%map c3 = infer_exp ~env else_exp exp_type in
      c1 &~ c2 &~ c3
    | Exp_sequence (exp1, exp2) ->
      let%bind c1 = infer_exp ~env exp1 Predef.unit in
      let%map c2 = infer_exp ~env exp2 exp_type in
      c1 &~ c2
    | Exp_constr (constr, arg_exp) ->
      (inst_constr
         ~env
         ~constr_name:constr
         ~constr_arity:(infer_constructor_arity arg_exp)
         ~constr_type:exp_type
       @@ fun arg_type ->
       match arg_exp, arg_type with
       | Some arg_exp, Some arg_type -> infer_exp ~env arg_exp arg_type >>| fun c -> (), c
       | None, None -> return ((), tt)
       | _ ->
         Or_error.error_s
           [%message
             "Constructor argument mistmatch in expression" (exp : Ast.expression)])
      >>| snd
    | Exp_match (match_exp, cases) ->
      exists' ~id_source
      @@ fun match_exp_type ->
      let%bind c1 = infer_exp ~env match_exp match_exp_type in
      let%map c2 = infer_cases ~env cases ~lhs_type:match_exp_type ~rhs_type:exp_type in
      c1 &~ c2

  and infer_exps ~env exps k =
    let open Or_error.Let_syntax in
    match exps with
    | [] -> k ([], Ok tt)
    | exp :: exps ->
      exists' ~id_source:(Env.id_source env)
      @@ fun exp_type ->
      let c1 = infer_exp ~env exp exp_type in
      infer_exps ~env exps
      @@ fun (exp_types, c2) ->
      k
        ( exp_type :: exp_types
        , let%map c1 = c1
          and c2 = c2 in
          c1 &~ c2 )

  and infer_cases ~env cases ~lhs_type ~rhs_type =
    let open Or_error.Let_syntax in
    let%map cs =
      cases |> List.map ~f:(infer_case ~env ~lhs_type ~rhs_type) |> Or_error.all
    in
    all cs

  and infer_case ~env { case_lhs = pat; case_rhs = exp } ~lhs_type ~rhs_type =
    bind_pat ~env pat lhs_type ~in_:(fun env -> infer_exp ~env exp rhs_type)

  and infer_value_binding
        ~(env : Env.t)
        { value_binding_var = var; value_binding_exp = exp }
        k
    =
    let open Or_error.Let_syntax in
    let exp_type_var = Type.Var.create ~id_source:(Env.id_source env) () in
    let exp_type = Type.var exp_type_var in
    let%bind c = infer_exp ~env exp exp_type in
    Env.rename_var env ~var ~in_:(fun env cvar ->
      let%map c' = k env in
      let_ cvar#=(poly_scheme ([ exp_type_var ] @. c @=> exp_type)) ~in_:c')
  ;;
end

module Structure = struct
  let infer_prim ~env value_desc k =
    let open Or_error.Let_syntax in
    let%bind quantifiers, type_ = Convert.core_scheme ~env value_desc.value_type in
    Env.rename_var env ~var:value_desc.value_name ~in_:(fun env cvar ->
      let%map c = k env in
      let_ cvar#=(poly_scheme (quantifiers @. tt @=> type_)) ~in_:c)
  ;;

  let infer_type_decl
        ~(env : Env.t)
        ~type_name
        ~type_arity
        ~type_ident
        { type_decl_name; type_decl_params; type_decl_kind }
    =
    let open Or_error.Let_syntax in
    assert (Type_name.(type_name = type_decl_name));
    (* Convert the declaration kind *)
    let%map type_kind =
      match type_decl_kind with
      | Type_decl_abstract -> return Adt.Type_abstract
      | Type_decl_variant constr_decls ->
        let constructor_type =
          Adt.Type_constr
            ( List.map type_decl_params ~f:(fun type_var -> Adt.Type_var type_var)
            , type_ident )
        in
        let%map constr_decls =
          List.map constr_decls ~f:(fun { constructor_name; constructor_arg } ->
            let constructor_ident =
              Adt.Constructor_ident.create
                ~id_source:(Env.id_source env)
                ~name:(constructor_name :> string)
                ()
            in
            let%map constructor_arg =
              constructor_arg
              |> Option.value_map
                   ~f:(fun arg -> Convert.Core_type.to_type_expr ~env arg >>| Option.some)
                   ~default:(return None)
            in
            { Adt.constructor_name
            ; constructor_ident
            ; constructor_alphas = type_decl_params
            ; constructor_type
            ; constructor_arg
            ; constructor_type_ident = type_ident
            })
          |> Or_error.all
        in
        Adt.Type_variant constr_decls
    in
    { Adt.type_name; type_ident; type_arity; type_kind }
  ;;

  let infer_type_decls ~env type_decls =
    let open Or_error.Let_syntax in
    let type_name_and_arities =
      List.map
        type_decls
        ~f:(fun { type_decl_name; type_decl_params; type_decl_kind = _ } ->
          type_decl_name, List.length type_decl_params)
    in
    (* 1. Declare all the types *)
    Env.declare_types env type_name_and_arities ~in_:(fun env_with_decls type_idents ->
      match
        List.map3
          type_name_and_arities
          type_idents
          type_decls
          ~f:(fun (type_name, type_arity) type_ident type_decl ->
            (* 2. Convert each declaration *)
            infer_type_decl
              ~env:env_with_decls
              ~type_name
              ~type_arity
              ~type_ident
              type_decl)
      with
      | Ok type_defs ->
        let%map type_defs = Or_error.all type_defs in
        (* 3. Define the types *)
        List.fold type_defs ~init:env ~f:Env.add_type_def
      | Unequal_lengths -> assert false)
  ;;

  let rec infer_str ~env (str : Ast.structure) =
    let open Or_error.Let_syntax in
    match str with
    | [] -> return tt
    | Str_type type_decls :: str ->
      let%bind env = infer_type_decls ~env type_decls in
      infer_str ~env str
    | Str_primitive value_desc :: str ->
      infer_prim ~env value_desc @@ fun env -> infer_str ~env str
    | Str_value value_binding :: str ->
      Expression.infer_value_binding ~env value_binding @@ fun env -> infer_str ~env str
  ;;
end
