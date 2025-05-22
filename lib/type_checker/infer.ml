open! Import
open Ast_types
open Ast
open Constraint

module Convert = struct
  let type_name ~env (type_name : Type_name.With_range.t) : Adt.Type_ident.t * int =
    (* If the type name is shadowed, pick the closest one *)
    match Env.find_type_def env type_name.it |> List.hd with
    | None -> Mlsus_error.(raise @@ unbound_type ~range:type_name.range type_name.it)
    | Some type_def -> type_def.type_ident, type_def.type_arity
  ;;

  module Core_type = struct
    let assert_expected_arity_is_equal_to_actual_arity
          ~(arg_types : _ With_range.t list)
          ~(expected_arity : int)
          ~(constr_name : Type_name.With_range.t)
      =
      let actual_arity = List.length arg_types in
      if expected_arity <> actual_arity
      then (
        let args_range =
          match arg_types with
          | type_ :: arg_types ->
            List.fold arg_types ~init:type_.range ~f:(fun range type_ ->
              Range.merge range type_.range)
          | [] ->
            (* For an empty args list, the correct range is the range of the type name *)
            constr_name.range
        in
        Mlsus_error.(
          raise
          @@ type_constructor_arity_mismatch
               ~args_range
               ~actual_arity
               ~expected_arity
               constr_name))
    ;;

    let rec to_type_expr ~env (type_ : Ast.core_type) : Adt.type_expr =
      match type_.it with
      | Type_var v -> Type_var v.it
      | Type_arrow (type1, type2) ->
        let type_expr1 = to_type_expr ~env type1
        and type_expr2 = to_type_expr ~env type2 in
        Type_arrow (type_expr1, type_expr2)
      | Type_tuple types ->
        let type_exprs = List.map types ~f:(to_type_expr ~env) in
        Type_tuple type_exprs
      | Type_constr (arg_types, constr_name) ->
        let type_ident, expected_arity = type_name ~env constr_name in
        assert_expected_arity_is_equal_to_actual_arity
          ~arg_types
          ~expected_arity
          ~constr_name;
        let arg_types = List.map arg_types ~f:(to_type_expr ~env) in
        Type_constr (arg_types, type_ident)
    ;;

    let rec to_type ~env (type_ : Ast.core_type) : Type.t =
      match type_.it with
      | Type_var v ->
        (match Env.find_type_var env v.it with
         | Some v -> Type.var v
         | None -> Mlsus_error.(raise @@ unbound_type_variable ~range:v.range v.it))
      | Type_arrow (type1, type2) ->
        let type1 = to_type ~env type1
        and type2 = to_type ~env type2 in
        Type.(type1 @-> type2)
      | Type_tuple types ->
        let types = types |> List.map ~f:(to_type ~env) in
        Type.tuple types
      | Type_constr (arg_types, constr_name) ->
        let type_ident, expected_arity = type_name ~env constr_name in
        assert_expected_arity_is_equal_to_actual_arity
          ~arg_types
          ~expected_arity
          ~constr_name;
        let arg_types = arg_types |> List.map ~f:(to_type ~env) in
        Type.constr arg_types type_ident
    ;;
  end

  let rec type_expr ~env (type_ : Adt.type_expr) : Type.t =
    match type_ with
    | Type_var v ->
      (match Env.find_type_var env v with
       | Some v -> Type.var v
       | None ->
         Mlsus_error.(
           raise
           @@ bug_s
                ~here:[%here]
                [%message "Expected variable to be bound in env" (v : Type_var_name.t)]))
    | Type_arrow (type_expr1, type_expr2) ->
      let type1 = type_expr ~env type_expr1
      and type2 = type_expr ~env type_expr2 in
      Type.(type1 @-> type2)
    | Type_tuple type_exprs ->
      let types = type_exprs |> List.map ~f:(type_expr ~env) in
      Type.tuple types
    | Type_constr (arg_type_exprs, constr) ->
      let arg_types = arg_type_exprs |> List.map ~f:(type_expr ~env) in
      Type.constr arg_types constr
  ;;

  let core_scheme ~(env : Env.t) (scheme : Ast.core_scheme)
    : (flexibility * Type.Var.t) list * Type.t
    =
    let { scheme_quantifiers; scheme_body } = scheme.it in
    let env, quantifiers =
      List.fold_map scheme_quantifiers ~init:env ~f:(fun env type_var ->
        Env.rename_type_var env ~type_var:type_var.it ~in_:(fun env ctype_var ->
          env, (Flexible, ctype_var)))
    in
    let body = Core_type.to_type ~env scheme_body in
    quantifiers, body
  ;;
end

let infer_constant const =
  match const with
  | Const_int _ -> Predef.int
  | Const_bool _ -> Predef.bool
  | Const_unit -> Predef.unit
;;

let infer_constructor_arity
      ~(constr_name : Constructor_name.With_range.t)
      (constr_arg : 'a With_range.t option)
  : Adt.constructor_arity With_range.t
  =
  match constr_arg with
  | None -> With_range.create ~range:constr_name.range Adt.Zero
  | Some x -> With_range.create ~range:x.range Adt.One
;;

let infer_constructor
      ~id_source
      ~constr_name
      ~constr_arg_range
      constr_def
      constr_arg'
      constr_type'
  =
  let { Adt.constructor_alphas
      ; constructor_arg
      ; constructor_type
      ; constructor_name = _
      ; constructor_type_ident = _
      }
    =
    constr_def
  in
  let raise_constructor_arity_mismatch ~expected_arity ~actual_arity =
    Mlsus_error.(
      raise
      @@ constructor_arity_mismatch
           ~arg_range:constr_arg_range
           ~expected_arity
           ~actual_arity
           constr_name)
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
  let c_constr_arg =
    match constr_arg', constructor_arg with
    | None, None -> tt
    | Some constr_arg', Some constr_arg ->
      let constr_arg = Convert.type_expr ~env constr_arg in
      Type.(var constr_arg' =~ constr_arg)
    | Some _, None ->
      raise_constructor_arity_mismatch ~expected_arity:`Zero ~actual_arity:`One
    | None, Some _ ->
      raise_constructor_arity_mismatch ~expected_arity:`One ~actual_arity:`Zero
  in
  let constr_type = Convert.type_expr ~env constructor_type in
  exists_many constr_vars @@ (Type.(var constr_type' =~ constr_type) &~ c_constr_arg)
;;

let infer_label ~id_source ~label_def label_arg' label_type' =
  let { Adt.label_alphas; label_arg; label_type; label_name = _; label_type_ident = _ } =
    label_def
  in
  let env, label_vars =
    List.fold_map label_alphas ~init:(Env.empty ~id_source ()) ~f:(fun env type_var ->
      Env.rename_type_var env ~type_var ~in_:(fun env cvar -> env, cvar))
  in
  let label_arg = Convert.type_expr ~env label_arg in
  let label_type = Convert.type_expr ~env label_type in
  exists_many label_vars
  @@ (Type.(var label_type' =~ label_type) &~ Type.(var label_arg' =~ label_arg))
;;

module Make_adt_inst (X : sig
    type name [@@deriving sexp_of]
    type def [@@deriving sexp_of]
    type arg_type [@@deriving sexp_of]
    type infer_ctx [@@deriving sexp_of]

    val find : Env.t -> name -> def list
    val unbound : range:Range.t -> name -> Mlsus_error.t
    val ident : def -> Type.Ident.t

    val infer
      :  def
      -> id_source:Identifier.source
      -> ctx:infer_ctx
      -> arg:arg_type
      -> ret:Type.Var.t
      -> Constraint.t

    val arg_closure : arg_type -> Type.Var.t list
  end) =
struct
  let inst ~env ~(name : X.name With_range.t) ~infer_ctx ~arg ~(ret : Type.Var.t) =
    match X.find env name.it with
    | [] -> Mlsus_error.(raise @@ X.unbound ~range:name.range name.it)
    | [ def ] ->
      (* The definition is unambiguous. Just infer immediately *)
      X.infer def ~id_source:(Env.id_source env) ~ctx:infer_ctx ~arg ~ret
    | defs ->
      (* Type-based disambiguation, filter the constructor definition in the environment with
         the type identifiers. *)
      let disambiguate_defs_by_type_ident type_ident =
        let open Adt in
        match List.filter defs ~f:(fun def -> Type_ident.(X.ident def = type_ident)) with
        | [ def ] -> def
        | [] ->
          Mlsus_error.(
            raise
            @@ bug_s
                 ~here:[%here]
                 [%message
                   "No definitions with expected type ident"
                     (name : X.name With_range.t)
                     (type_ident : Type_ident.t)])
        | defs ->
          Mlsus_error.(
            raise
            @@ bug_s
                 ~here:[%here]
                 [%message
                   "Ambiguous definitions with expected type ident"
                     (name : X.name With_range.t)
                     (defs : X.def list)
                     (type_ident : Type_ident.t)])
      in
      let disambiguate_and_infer type_ident =
        let def = disambiguate_defs_by_type_ident type_ident in
        X.infer def ~id_source:(Env.id_source env) ~ctx:infer_ctx ~arg ~ret
      in
      let hd_type = Type.Var.create ~id_source:(Env.id_source env) () in
      let spine_type = Type.Var.create ~id_source:(Env.id_source env) () in
      exists_many [ hd_type; spine_type ]
      @@ (Type.(var ret =~ var spine_type @% var hd_type)
          &~ lower hd_type
          &~ match_
               hd_type
               ~closure:([ ret; hd_type ] @ X.arg_closure arg)
               ~with_:(function
                 | App _ | Spine _ -> assert false
                 | (Head (Arrow | Tuple _ | Scheme _ | Poly) | Rigid_var) as matchee ->
                   let type_head =
                     match matchee with
                     | Head Arrow -> `Arrow
                     | Head (Tuple _) -> `Tuple
                     | Head Poly -> `Poly
                     | Head (Scheme _) -> `Scheme
                     | Rigid_var -> `Rigid_var
                     | _ -> assert false
                   in
                   ff
                     (Mlsus_error.disambiguation_mismatched_type
                        ~range:name.range
                        ~type_head)
                 | Head (Constr type_ident) -> disambiguate_and_infer type_ident)
               ~else_:(fun () ->
                 let default_type_ident = X.ident (List.hd_exn defs) in
                 Type.(var hd_type =~ hd (Constr default_type_ident))))
  ;;
end

module Constructor_inst = Make_adt_inst (struct
    type name = Constructor_name.t [@@deriving sexp_of]
    type def = Adt.constructor_definition [@@deriving sexp_of]
    type arg_type = Type.Var.t option [@@deriving sexp_of]
    type infer_ctx = Constructor_name.With_range.t * Range.t [@@deriving sexp_of]

    let find env name = Env.find_constr env name
    let unbound ~range name = Mlsus_error.unbound_constructor ~range name
    let ident def = def.Adt.constructor_type_ident

    let infer def ~id_source ~ctx:(constr_name, constr_arg_range) ~arg ~ret =
      infer_constructor ~id_source ~constr_name ~constr_arg_range def arg ret
    ;;

    let arg_closure arg =
      match arg with
      | None -> []
      | Some arg -> [ arg ]
    ;;
  end)

module Label_inst = Make_adt_inst (struct
    type name = Label_name.t [@@deriving sexp_of]
    type def = Adt.label_definition [@@deriving sexp_of]
    type arg_type = Type.Var.t [@@deriving sexp_of]
    type infer_ctx = unit [@@deriving sexp_of]

    let find env name = Env.find_label env name
    let unbound ~range name = Mlsus_error.unbound_label ~range name
    let ident def = def.Adt.label_type_ident

    let infer def ~id_source ~ctx:() ~arg ~ret =
      infer_label ~id_source ~label_def:def arg ret
    ;;

    let arg_closure arg = [ arg ]
  end)

let exists_opt opt_var cst =
  match opt_var with
  | None -> cst
  | Some var -> exists var cst
;;

let inst_constr
      ~(env : Env.t)
      ~(constr_name : Constructor_name.With_range.t)
      ~(constr_arity : Adt.constructor_arity With_range.t)
      ~constr_type
      k
  =
  let constr_arg_range = constr_arity.range in
  let constr_arg =
    match constr_arity.it with
    | Zero -> None
    | One -> Some (Type.Var.create ~id_source:(Env.id_source env) ())
  in
  let c_type =
    Constructor_inst.inst
      ~env
      ~name:constr_name
      ~infer_ctx:(constr_name, constr_arg_range)
      ~arg:constr_arg
      ~ret:constr_type
  in
  let result, c_arg = k constr_arg in
  result, exists_opt constr_arg (c_arg &~ c_type)
;;

let inst_label ~(env : Env.t) ~(label_name : Label_name.With_range.t) ~label_type k =
  let label_arg = Type.Var.create ~id_source:(Env.id_source env) () in
  let c_type =
    Label_inst.inst ~env ~name:label_name ~infer_ctx:() ~arg:label_arg ~ret:label_type
  in
  let result, c_arg = k label_arg in
  result, exists label_arg (c_arg &~ c_type)
;;

module Pattern = struct
  module Fragment = struct
    type t = { var_bindings : Type.Var.t Var_name.Map.t } [@@deriving sexp_of]

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
    let a = Type.Var.create ~id_source () in
    let result, c = f a in
    result, exists a c
  ;;

  let with_range' (result, c) ~range = result, with_range ~range c

  let rec infer_pat ~env (pat : pattern) (pat_type : Type.Var.t) k =
    with_range' ~range:pat.range
    @@
    match pat.it with
    | Pat_any -> k (Fragment.empty, tt)
    | Pat_var x -> k (Fragment.singleton x.it pat_type, tt)
    | Pat_alias (pat, x) ->
      infer_pat ~env pat pat_type
      @@ fun (f, c) ->
      let f = Fragment.extend f ~var:x.it ~type_:pat_type in
      k (f, c)
    | Pat_const const -> k (Fragment.empty, Type.(var pat_type =~ infer_constant const))
    | Pat_tuple pats ->
      infer_pats ~env pats
      @@ fun (f, pat_types, c) ->
      k (f, c &~ Type.(var pat_type =~ tuple (List.map ~f:var pat_types)))
    | Pat_constr (constr_name, arg_pat) ->
      inst_constr
        ~env
        ~constr_name
        ~constr_arity:(infer_constructor_arity ~constr_name arg_pat)
        ~constr_type:pat_type
      @@ fun arg_type ->
      (match arg_pat, arg_type with
       | Some arg_pat, Some arg_type -> infer_pat ~env arg_pat arg_type k
       | None, None -> k (Fragment.empty, tt)
       | _ ->
         (* Note that arity mismatches are caught by [infer_constructor] *)
         Mlsus_error.(
           raise
           @@ bug_s
                ~here:[%here]
                [%message "Constructor argument mistmatch in pattern" (pat : Ast.pattern)]))
    | Pat_record label_pats -> infer_label_pats ~env ~record_type:pat_type label_pats k
    | Pat_annot (pat, annot) ->
      let type_ = Convert.Core_type.to_type ~env annot in
      infer_pat ~env pat pat_type @@ fun (f, c) -> k (f, Type.(var pat_type =~ type_) &~ c)

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

  and infer_label_pats ~env ~record_type label_pats k =
    match label_pats with
    | [] -> k (Fragment.empty, tt)
    | (label_name, arg_pat) :: label_pats ->
      infer_label_pat ~env ~label_type:record_type label_name arg_pat
      @@ fun (f, c1) ->
      infer_label_pats ~env ~record_type label_pats
      @@ fun (f', c2) -> k (Fragment.merge f f', c1 &~ c2)

  and infer_label_pat ~env ~label_type label_name arg_pat k =
    inst_label ~env ~label_name ~label_type
    @@ fun arg_type -> infer_pat ~env arg_pat arg_type k
  ;;
end

module Expression = struct
  let exists' ~id_source f =
    let a = Type.Var.create ~id_source () in
    exists a (f a)
  ;;

  let exists_many' ~id_source n f =
    let as_ = List.init n ~f:(fun _ -> Type.Var.create ~id_source ()) in
    exists_many as_ (f as_)
  ;;

  let bind_pat ~env (pat : pattern) pat_type ~in_ =
    (Pattern.infer_pat ~env pat pat_type
     @@ fun (fragment, c) ->
     let env, bindings =
       fragment
       |> Pattern.Fragment.to_alist
       |> List.fold_map ~init:env ~f:(fun env (var, type_) ->
         Env.rename_var env ~var ~in_:(fun env cvar -> env, (cvar, type_)))
     in
     let in_ = in_ env in
     ( ()
     , c
       &~ List.fold bindings ~init:in_ ~f:(fun in_ (cvar, type_) ->
         let_ cvar#=(mono_scheme (Type.var type_)) ~in_) ))
    |> snd
  ;;

  let rec bind_pats ~env pat_and_types ~in_ =
    match pat_and_types with
    | [] -> in_ env
    | (pat, pat_type) :: pat_and_types ->
      bind_pat ~env pat pat_type ~in_:(fun env -> bind_pats ~env pat_and_types ~in_)
  ;;

  let rec infer_exp ~(env : Env.t) (exp : expression) (exp_type : Type.Var.t) =
    let id_source = Env.id_source env in
    with_range ~range:exp.range
    @@
    match exp.it with
    | Exp_var var ->
      (match Env.find_var env var.it with
       | Some var -> inst var (Type.var exp_type)
       | None -> Mlsus_error.(raise @@ unbound_variable ~range:var.range var.it))
    | Exp_const const -> Type.(var exp_type =~ infer_constant const)
    | Exp_fun (pats, exp) ->
      exists_many' ~id_source (List.length pats)
      @@ fun as1 ->
      exists' ~id_source
      @@ fun a2 ->
      let pat_and_types = List.zip_exn pats as1 in
      let c = bind_pats ~env pat_and_types ~in_:(fun env -> infer_exp ~env exp a2) in
      let arr_type =
        List.fold_right as1 ~init:(Type.var a2) ~f:(fun a1 arr -> Type.(var a1 @-> arr))
      in
      Type.(var exp_type =~ arr_type) &~ c
    | Exp_app (exp1, exp2) ->
      exists' ~id_source
      @@ fun a1 ->
      exists' ~id_source
      @@ fun a2 ->
      let c1 = infer_exp ~env exp1 a2 in
      let c2 = infer_exp ~env exp2 a1 in
      Type.(var a2 =~ var a1 @-> var exp_type) &~ c1 &~ c2
    | Exp_let (value_binding, exp) ->
      infer_value_binding ~env value_binding @@ fun env -> infer_exp ~env exp exp_type
    | Exp_exists (type_vars, exp) ->
      let env, type_vars =
        List.fold_map type_vars ~init:env ~f:(fun env type_var ->
          Env.rename_type_var env ~type_var:type_var.it ~in_:(fun env ctype_var ->
            env, ctype_var))
      in
      let c = infer_exp ~env exp exp_type in
      exists_many type_vars c
    | Exp_forall (type_vars, exp) ->
      let env, rigid_type_vars =
        List.fold_map type_vars ~init:env ~f:(fun env type_var ->
          Env.rename_type_var env ~type_var:type_var.it ~in_:(fun env ctype_var ->
            env, (Rigid, ctype_var)))
      in
      let exp_type' = Type.Var.create ~id_source:(Env.id_source env) () in
      let c = infer_exp ~env exp exp_type' in
      let x = Var.create ~id_source:(Env.id_source env) () in
      let_
        x#=(poly_scheme
              (((Flexible, exp_type') :: rigid_type_vars) @. c @=> Type.var exp_type'))
        ~in_:(inst x (Type.var exp_type))
    | Exp_annot (exp, annot) ->
      let annot = Convert.Core_type.to_type ~env annot in
      let c = infer_exp ~env exp exp_type in
      Type.(var exp_type =~ annot) &~ c
    | Exp_tuple exps ->
      infer_exps ~env exps
      @@ fun (exp_types, c) ->
      Type.(var exp_type =~ tuple (List.map ~f:var exp_types)) &~ c
    | Exp_if_then_else (if_exp, then_exp, else_exp) ->
      exists' ~id_source
      @@ fun if_type ->
      let c1 = infer_exp ~env if_exp if_type in
      let c2 = infer_exp ~env then_exp exp_type in
      let c3 = infer_exp ~env else_exp exp_type in
      Type.(var if_type =~ Predef.bool) &~ c1 &~ c2 &~ c3
    | Exp_sequence (exp1, exp2) ->
      exists' ~id_source
      @@ fun exp1_type ->
      let c1 = infer_exp ~env exp1 exp1_type in
      let c2 = infer_exp ~env exp2 exp_type in
      Type.(var exp1_type =~ Predef.unit) &~ c1 &~ c2
    | Exp_constr (constr_name, arg_exp) ->
      (inst_constr
         ~env
         ~constr_name
         ~constr_arity:(infer_constructor_arity ~constr_name arg_exp)
         ~constr_type:exp_type
       @@ fun arg_type ->
       match arg_exp, arg_type with
       | Some arg_exp, Some arg_type -> (), infer_exp ~env arg_exp arg_type
       | None, None -> (), tt
       | _ ->
         Mlsus_error.(
           raise
           @@ bug_s
                ~here:[%here]
                [%message
                  "Constructor argument mistmatch in expression" (exp : Ast.expression)])
      )
      |> snd
    | Exp_match (match_exp, cases) ->
      exists' ~id_source
      @@ fun match_exp_type ->
      let c1 = infer_exp ~env match_exp match_exp_type in
      let c2 = infer_cases ~env cases ~lhs_type:match_exp_type ~rhs_type:exp_type in
      c1 &~ c2
    | Exp_record label_exps -> infer_label_exps ~env ~record_type:exp_type label_exps
    | Exp_field (exp, label_name) ->
      exists' ~id_source
      @@ fun record_type ->
      let c1 = infer_exp ~env exp record_type in
      let (), c2 =
        inst_label ~env ~label_name ~label_type:record_type
        @@ fun arg_type -> (), Type.(var exp_type =~ var arg_type)
      in
      c1 &~ c2

  and infer_exps ~env exps k =
    match exps with
    | [] -> k ([], tt)
    | exp :: exps ->
      exists' ~id_source:(Env.id_source env)
      @@ fun exp_type ->
      let c1 = infer_exp ~env exp exp_type in
      infer_exps ~env exps @@ fun (exp_types, c2) -> k (exp_type :: exp_types, c1 &~ c2)

  and infer_label_exps ~env ~record_type label_exps =
    let cs =
      label_exps
      |> List.map ~f:(fun (label_name, arg_exp) ->
        infer_label_exp ~env ~label_type:record_type label_name arg_exp)
    in
    all cs

  and infer_label_exp ~env ~label_type label_name arg_exp =
    (inst_label ~env ~label_name ~label_type
     @@ fun arg_type -> (), infer_exp ~env arg_exp arg_type)
    |> snd

  and infer_cases ~env cases ~lhs_type ~rhs_type =
    let cs = cases |> List.map ~f:(infer_case ~env ~lhs_type ~rhs_type) in
    all cs

  and infer_case ~env case ~lhs_type ~rhs_type =
    let { case_lhs = pat; case_rhs = exp } = case.it in
    bind_pat ~env pat lhs_type ~in_:(fun env -> infer_exp ~env exp rhs_type)

  and infer_value_binding ~(env : Env.t) value_binding k =
    let { value_binding_var = var; value_binding_exp = exp } = value_binding.it in
    let exp_type = Type.Var.create ~id_source:(Env.id_source env) () in
    let c = infer_exp ~env exp exp_type in
    Env.rename_var env ~var:var.it ~in_:(fun env cvar ->
      let c' = k env in
      let_ cvar#=(poly_scheme ([ Flexible, exp_type ] @. c @=> Type.var exp_type)) ~in_:c')
  ;;
end

module Structure = struct
  let infer_prim ~env (value_desc : value_description) k =
    let { value_type; value_name } = value_desc.it in
    let quantifiers, type_ = Convert.core_scheme ~env value_type in
    Env.rename_var env ~var:value_name.it ~in_:(fun env cvar ->
      let c = k env in
      let_ cvar#=(poly_scheme (quantifiers @. tt @=> type_)) ~in_:c)
  ;;

  let infer_type_decl
        ~(env : Env.t)
        ~type_name
        ~type_arity
        ~type_ident
        (type_decl : type_declaration)
    =
    let { type_decl_name; type_decl_params; type_decl_kind } = type_decl.it in
    assert (Type_name.(type_name = type_decl_name.it));
    (* Convert the declaration kind *)
    let type_kind =
      match type_decl_kind with
      | Type_decl_abstract -> Adt.Type_abstract
      | Type_decl_variant constr_decls ->
        let constructor_type =
          Adt.Type_constr
            ( List.map type_decl_params ~f:(fun type_var -> Adt.Type_var type_var.it)
            , type_ident )
        in
        let constr_decls =
          List.map constr_decls ~f:(fun { constructor_name; constructor_arg } ->
            let constructor_arg =
              Option.map constructor_arg ~f:(Convert.Core_type.to_type_expr ~env)
            in
            { Adt.constructor_name = constructor_name.it
            ; constructor_alphas = List.map type_decl_params ~f:With_range.it
            ; constructor_type
            ; constructor_arg
            ; constructor_type_ident = type_ident
            })
        in
        Adt.Type_variant constr_decls
      | Type_decl_record label_decls ->
        let label_type =
          Adt.Type_constr
            ( List.map type_decl_params ~f:(fun type_var -> Adt.Type_var type_var.it)
            , type_ident )
        in
        let label_defs =
          List.map label_decls ~f:(fun { label_name; label_arg } ->
            let label_arg = Convert.Core_type.to_type_expr ~env label_arg in
            { Adt.label_name = label_name.it
            ; label_alphas = List.map type_decl_params ~f:With_range.it
            ; label_arg
            ; label_type
            ; label_type_ident = type_ident
            })
        in
        Adt.Type_record label_defs
    in
    { Adt.type_name; type_ident; type_arity; type_kind }
  ;;

  let infer_type_decls ~env (type_decls : type_declaration list) =
    let type_name_and_arities =
      List.map type_decls ~f:(fun type_decl ->
        let { type_decl_name; type_decl_params; type_decl_kind = _ } = type_decl.it in
        type_decl_name.it, List.length type_decl_params)
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
        (* 3. Define the types *)
        List.fold type_defs ~init:env ~f:Env.add_type_def
      | Unequal_lengths -> assert false)
  ;;

  let rec infer_str ~env (str : Ast.structure) =
    match str with
    | [] -> tt
    | { it = Str_type type_decls; range } :: str ->
      let env = infer_type_decls ~env type_decls in
      with_range ~range @@ infer_str ~env str
    | { it = Str_primitive value_desc; range } :: str ->
      with_range ~range @@ infer_prim ~env value_desc @@ fun env -> infer_str ~env str
    | { it = Str_value value_binding; range } :: str ->
      with_range ~range
      @@ Expression.infer_value_binding ~env value_binding
      @@ fun env -> infer_str ~env str
  ;;
end
