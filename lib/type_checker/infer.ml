open! Import
open Ast_types
open Ast
open Constraint

let assert_with_fcp ~env ~range =
  if not (Omniml_options.is_enabled (Env.options env) First_class_polymorphism)
  then Omniml_error.(raise @@ fcp_disabled ~range)
;;

module Convert = struct
  let type_name ~env (type_name : Type_name.With_range.t)
    : [ `Alias of Adt.alias_definition | `Newtype of Adt.Type_ident.t ] * int
    =
    (* If the type name is shadowed, pick the closest one *)
    match Env.find_type_def env type_name.it |> List.hd with
    | None -> Omniml_error.(raise @@ unbound_type ~range:type_name.range type_name.it)
    | Some type_def ->
      ( (match type_def.type_kind with
         | Type_alias alias_def -> `Alias alias_def
         | _ -> `Newtype type_def.type_ident)
      , type_def.type_arity )
  ;;

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
      Omniml_error.(
        raise
        @@ type_constructor_arity_mismatch
             ~args_range
             ~actual_arity
             ~expected_arity
             constr_name))
  ;;

  let rec core_type_to_type_expr
            ~env
            ?(subst = Type_var_name.Map.empty)
            (type_ : Ast.core_type)
    : Adt.type_expr
    =
    let self ?(subst = subst) = core_type_to_type_expr ~env ~subst in
    match type_.it with
    | Type_var v ->
      (match Map.find subst v.it with
       | None -> Type_var v.it
       | Some type_expr -> type_expr)
    | Type_arrow (param_type, ret_type) ->
      let type_expr1 = self param_type
      and type_expr2 = self ret_type in
      Type_arrow (type_expr1, type_expr2)
    | Type_tuple types ->
      let type_exprs = List.map types ~f:self in
      Type_tuple type_exprs
    | Type_constr (arg_types, constr_name) ->
      let newtype_or_alias, expected_arity = type_name ~env constr_name in
      assert_expected_arity_is_equal_to_actual_arity
        ~arg_types
        ~expected_arity
        ~constr_name;
      let arg_types = List.map arg_types ~f:self in
      (match newtype_or_alias with
       | `Newtype type_ident -> Type_constr (arg_types, type_ident)
       | `Alias alias_def ->
         let subst =
           List.fold2_exn
             alias_def.alias_alphas
             arg_types
             ~init:subst
             ~f:(fun subst alias_alpha arg_type ->
               Map.set subst ~key:alias_alpha ~data:arg_type)
         in
         self ~subst alias_def.alias_type)
    | Type_scheme scheme ->
      assert_with_fcp ~env ~range:type_.range;
      let scheme = core_scheme_to_type_scheme_expr ~env ~subst scheme in
      Type_scheme scheme
    | Type_poly scheme ->
      let scheme = core_scheme_to_type_scheme_expr ~env ~subst scheme in
      Type_poly scheme

  and core_scheme_to_type_scheme_expr
        ~env
        ?(subst = Type_var_name.Map.empty)
        (scheme : Ast.core_scheme)
    : Adt.type_scheme_expr
    =
    let { scheme_quantifiers; scheme_body } = scheme.it in
    let scheme_quantifiers = List.map scheme_quantifiers ~f:With_range.it in
    let scheme_body = core_type_to_type_expr ~env ~subst scheme_body in
    Adt.create_type_scheme_expr ~quantifiers:scheme_quantifiers scheme_body
  ;;

  let rec core_type_to_type
            ~env
            ?(subst = Type_var_name.Map.empty)
            (type_ : Ast.core_type)
    : Type.t
    =
    let self ?(subst = subst) = core_type_to_type ~env ~subst in
    match type_.it with
    | Type_var v ->
      (match Map.find subst v.it with
       | Some type_ -> type_
       | None ->
         (match Env.find_type_var env v.it with
          | Some v -> Type.var v
          | None -> Omniml_error.(raise @@ unbound_type_variable ~range:v.range v.it)))
    | Type_arrow (param_type, ret_type) ->
      let type1 = self param_type
      and type2 = self ret_type in
      Type.(type1 @-> type2)
    | Type_tuple types ->
      let types = types |> List.map ~f:self in
      Type.tuple types
    | Type_constr (arg_types, constr_name) ->
      let newtype_or_alias, expected_arity = type_name ~env constr_name in
      assert_expected_arity_is_equal_to_actual_arity
        ~arg_types
        ~expected_arity
        ~constr_name;
      let arg_types = arg_types |> List.map ~f:self in
      (match newtype_or_alias with
       | `Newtype type_ident -> Type.constr arg_types type_ident
       | `Alias alias_def ->
         let subst =
           List.fold2_exn
             alias_def.alias_alphas
             arg_types
             ~init:subst
             ~f:(fun subst alias_alpha arg_type ->
               Map.set subst ~key:alias_alpha ~data:arg_type)
         in
         self ~subst alias_def.alias_type)
    | Type_scheme scheme ->
      assert_with_fcp ~env ~range:type_.range;
      let scheme = core_scheme_to_type_scheme ~env ~subst scheme in
      Type.scheme scheme
    | Type_poly scheme ->
      let scheme = core_scheme_to_type_scheme ~env ~subst scheme in
      Type.poly scheme

  and core_scheme_to_type_scheme ~env ?(subst = Type_var_name.Map.empty) scheme
    : Type.Scheme.t
    =
    let { scheme_quantifiers; scheme_body } = scheme.it in
    let env, scheme_quantifiers =
      List.fold_map scheme_quantifiers ~init:env ~f:(fun env type_var ->
        Env.rename_type_var env ~type_var:type_var.it ~in_:(fun env ctype_var ->
          env, ctype_var))
    in
    let scheme_body = core_type_to_type ~env ~subst scheme_body in
    Type.Scheme.create ~quantifiers:scheme_quantifiers scheme_body
  ;;

  let rec type_expr ~env (type_ : Adt.type_expr) : Type.t =
    match type_ with
    | Type_var v ->
      (match Env.find_type_var env v with
       | Some v -> Type.var v
       | None ->
         Omniml_error.(
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
    | Type_scheme scheme -> Type.scheme (type_scheme_expr ~env scheme)
    | Type_poly scheme -> Type.poly (type_scheme_expr ~env scheme)

  and type_scheme_expr ~env { scheme_quantifiers; scheme_body } : Type.Scheme.t =
    let env, scheme_quantifiers =
      List.fold_map scheme_quantifiers ~init:env ~f:(fun env type_var ->
        Env.rename_type_var env ~type_var ~in_:(fun env ctype_var -> env, ctype_var))
    in
    let scheme_body = type_expr ~env scheme_body in
    Type.Scheme.create ~quantifiers:scheme_quantifiers scheme_body
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
      ~env
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
    Omniml_error.(
      raise
      @@ constructor_arity_mismatch
           ~arg_range:constr_arg_range
           ~expected_arity
           ~actual_arity
           constr_name)
  in
  (* Bind [alphas] existentially *)
  let env, constr_vars =
    List.fold_map constructor_alphas ~init:(Env.local env) ~f:(fun env type_var ->
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
  exists_many constr_vars @@ (Type.(var constr_type' =~ constr_type) >> c_constr_arg)
;;

let infer_label ~env ~label_def label_arg' label_type' =
  let { Adt.label_alphas; label_arg; label_type; label_name = _; label_type_ident = _ } =
    label_def
  in
  let env, label_vars =
    List.fold_map label_alphas ~init:(Env.local env) ~f:(fun env type_var ->
      Env.rename_type_var env ~type_var ~in_:(fun env cvar -> env, cvar))
  in
  let label_arg = Convert.type_expr ~env label_arg in
  let label_type = Convert.type_expr ~env label_type in
  exists_many label_vars
  @@ (Type.(var label_type' =~ label_type) >> Type.(var label_arg' =~ label_arg))
;;

module Make_adt_inst (X : sig
    type name [@@deriving sexp_of]
    type def [@@deriving sexp_of]
    type arg_type [@@deriving sexp_of]
    type infer_ctx [@@deriving sexp_of]

    val find : Env.t -> name -> def list
    val unbound : range:Range.t -> name -> Omniml_error.t
    val ident : def -> Type.Ident.t

    (** [def_ret_shape d] returns the shape of the return type of the definition [d]. *)
    val def_ret_shape : def -> Type_var_name.t list * Type.Ident.t

    val infer
      :  def
      -> env:Env.t
      -> ctx:infer_ctx
      -> arg:arg_type
      -> ret:Type.Var.t
      -> unit Constraint.t

    val arg_closure : arg_type -> Type.Var.t list
    val ambiguous : range:Range.t -> Omniml_error.t
  end) =
struct
  let inst ~env ~(name : X.name With_range.t) ~infer_ctx ~arg ~(ret : Type.Var.t) =
    match X.find env name.it with
    | [] -> Omniml_error.(raise @@ X.unbound ~range:name.range name.it)
    | [ def ] ->
      (* The definition is unambiguous. Just infer immediately *)
      X.infer def ~env ~ctx:infer_ctx ~arg ~ret
    | defs ->
      let id_source = Env.id_source env in
      (* Type-based disambiguation, filter the constructor definition in the environment with
         the type identifiers. *)
      let disambiguate_defs_by_type_ident type_ident =
        let open Adt in
        match List.filter defs ~f:(fun def -> Type_ident.(X.ident def = type_ident)) with
        | [ def ] -> def
        | [] ->
          Omniml_error.(
            raise
            @@ bug_s
                 ~here:[%here]
                 [%message
                   "No definitions with expected type ident"
                     (name : X.name With_range.t)
                     (type_ident : Type_ident.t)])
        | defs ->
          Omniml_error.(
            raise
            @@ bug_s
                 ~here:[%here]
                 [%message
                   "Ambiguous definitions with expected type ident"
                     (name : X.name With_range.t)
                     (defs : X.def list)
                     (type_ident : Type_ident.t)])
      in
      let disambiguate_and_infer args type_ident =
        let ret = Type.Var.create ~id_source () in
        let def = disambiguate_defs_by_type_ident type_ident in
        exists ret
        @@ (Type.(var ret =~ constr (List.map args ~f:var) type_ident)
            >> X.infer def ~env ~ctx:infer_ctx ~arg ~ret)
      in
      (* Matches on [ret], if its a constructor then we can disambiguate it. 
         If [ret] is never unified, it is unified with the default shape (the 
         lexically closest matching definition) *)
      match_
        ret
        ~closure:(X.arg_closure arg |> List.map ~f:(fun v -> `Type v))
        ~with_:(function
          | (Arrow (_, _) | Tuple _ | Scheme _ | Poly _) as matchee ->
            let type_head =
              match matchee with
              | Arrow (_, _) -> `Arrow
              | Tuple _ -> `Tuple
              | Scheme _ | Poly _ -> `Poly
              | _ -> assert false
            in
            ff (Omniml_error.disambiguation_mismatched_type ~range:name.range ~type_head)
          | Constr (args, type_ident) -> disambiguate_and_infer args type_ident)
        ~error:(fun _ -> X.ambiguous ~range:name.range)
        ~default:(fun () ->
          let default_type_def = List.hd_exn defs in
          let ret_alphas, ret_constr = X.def_ret_shape default_type_def in
          Shape (Principal_shape.constr ~arity:(List.length ret_alphas) ret_constr))
  ;;
end

module Constructor_inst = Make_adt_inst (struct
    type name = Constructor_name.t [@@deriving sexp_of]
    type def = Adt.constructor_definition [@@deriving sexp_of]
    type arg_type = Type.Var.t option [@@deriving sexp_of]
    type infer_ctx = Constructor_name.With_range.t * Range.t [@@deriving sexp_of]

    let find env name = Env.find_constr env name
    let unbound ~range name = Omniml_error.unbound_constructor ~range name
    let ident def = def.Adt.constructor_type_ident
    let def_ret_shape (def : def) = def.constructor_alphas, def.constructor_type_ident

    let infer def ~env ~ctx:(constr_name, constr_arg_range) ~arg ~ret =
      infer_constructor ~env ~constr_name ~constr_arg_range def arg ret
    ;;

    let arg_closure arg =
      match arg with
      | None -> []
      | Some arg -> [ arg ]
    ;;

    let ambiguous = Omniml_error.ambiguous_constructor
  end)

module Label_inst = Make_adt_inst (struct
    type name = Label_name.t [@@deriving sexp_of]
    type def = Adt.label_definition [@@deriving sexp_of]
    type arg_type = Type.Var.t [@@deriving sexp_of]
    type infer_ctx = unit [@@deriving sexp_of]

    let find env name = Env.find_label env name
    let unbound ~range name = Omniml_error.unbound_label ~range name
    let ident def = def.Adt.label_type_ident
    let def_ret_shape (def : def) = def.label_alphas, def.label_type_ident
    let infer def ~env ~ctx:() ~arg ~ret = infer_label ~env ~label_def:def arg ret
    let arg_closure arg = [ arg ]
    let ambiguous = Omniml_error.ambiguous_label
  end)

let inst_constr
      ~(env : Env.t)
      ~(constr_name : Constructor_name.With_range.t)
      ~(constr_arity : Adt.constructor_arity With_range.t)
      ~constr_type
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
  constr_arg, c_type
;;

let inst_label ~(env : Env.t) ~(label_name : Label_name.With_range.t) ~label_type =
  let label_arg = Type.Var.create ~id_source:(Env.id_source env) () in
  let c_type =
    Label_inst.inst ~env ~name:label_name ~infer_ctx:() ~arg:label_arg ~ret:label_type
  in
  label_arg, c_type
;;

module Pattern = struct
  module Fragment = struct
    type t =
      { var_bindings : Type.Var.t With_range.t Var_name.Map.t
      ; exist_bindings : Type.Var.t list
      }
    [@@deriving sexp_of]

    let empty = { var_bindings = Var_name.Map.empty; exist_bindings = [] }

    let singleton (var : Var_name.With_range.t) type_ =
      { var_bindings =
          Var_name.Map.singleton var.it (With_range.create ~range:var.range type_)
      ; exist_bindings = []
      }
    ;;

    let extend t ~(var : Var_name.With_range.t) ~type_ =
      match
        Map.add
          t.var_bindings
          ~key:var.it
          ~data:(With_range.create ~range:var.range type_)
      with
      | `Ok var_bindings -> { t with var_bindings }
      | `Duplicate ->
        let fst_range = (Map.find_exn t.var_bindings var.it).range in
        Omniml_error.(raise @@ non_linear_pattern var.it ~fst_range ~snd_range:var.range)
    ;;

    let exists t type_var = { t with exist_bindings = type_var :: t.exist_bindings }
  end

  module With_fragment = struct
    module T = struct
      type 'a t = Fragment.t -> Fragment.t * 'a

      let return x = fun fragment -> fragment, x

      let bind t ~f =
        fun fragment ->
        let fragment, x = t fragment in
        f x fragment
      ;;

      let map = `Define_using_bind
    end

    include T
    include Monad.Make (T)

    let perform_exists type_var = fun fragment -> Fragment.exists fragment type_var, ()

    let perform_extend ~var ~type_ =
      fun fragment -> Fragment.extend fragment ~var ~type_, ()
    ;;

    let exists ~id_source f =
      let open Let_syntax in
      let a = Type.Var.create ~id_source () in
      let%bind () = perform_exists a in
      f a
    ;;

    let with_range t ~range = map t ~f:(fun c -> with_range ~range c)

    let inst_label ~env ~label_name ~label_type k =
      let open Let_syntax in
      let label_arg, c_label = inst_label ~env ~label_name ~label_type in
      let%bind () = perform_exists label_arg in
      let%map c_arg = k label_arg in
      c_label >> c_arg
    ;;

    let inst_constr ~env ~constr_name ~constr_arity ~constr_type k =
      let open Let_syntax in
      let constr_arg, c_label =
        inst_constr ~env ~constr_name ~constr_arity ~constr_type
      in
      let%bind () = Option.value_map constr_arg ~f:perform_exists ~default:(return ()) in
      let%map c_arg = k constr_arg in
      c_label >> c_arg
    ;;

    let run t = t Fragment.empty
  end

  let rec infer_pat ~env (pat : pattern) (pat_type : Type.Var.t) =
    let open With_fragment in
    let open Let_syntax in
    with_range ~range:pat.range
    @@
    match pat.it with
    | Pat_any -> return tt
    | Pat_var x ->
      let%map () = perform_extend ~var:x ~type_:pat_type in
      tt
    | Pat_alias (pat, x) ->
      let%bind cpat = infer_pat ~env pat pat_type in
      let%map () = perform_extend ~var:x ~type_:pat_type in
      cpat
    | Pat_const const -> return @@ Type.(var pat_type =~ infer_constant const)
    | Pat_tuple pats ->
      let%map pat_types, cpats = infer_pats ~env pats in
      cpats >> Type.(var pat_type =~ tuple (List.map ~f:var pat_types))
    | Pat_constr (constr_name, arg_pat) ->
      inst_constr
        ~env
        ~constr_name
        ~constr_arity:(infer_constructor_arity ~constr_name arg_pat)
        ~constr_type:pat_type
      @@ fun arg_type ->
      (match arg_pat, arg_type with
       | Some arg_pat, Some arg_type -> infer_pat ~env arg_pat arg_type
       | None, None -> return tt
       | _ ->
         (* Note that arity mismatches are caught by [infer_constructor] *)
         Omniml_error.(
           raise
           @@ bug_s
                ~here:[%here]
                [%message "Constructor argument mistmatch in pattern" (pat : Ast.pattern)]))
    | Pat_record label_pats -> infer_label_pats ~env ~record_type:pat_type label_pats
    | Pat_annot (pat, annot) ->
      let type_ = Convert.core_type_to_type ~env annot in
      let%map c = infer_pat ~env pat pat_type in
      Type.(var pat_type =~ type_) >> c

  and infer_pats ~env pats =
    let open With_fragment in
    let open Let_syntax in
    match pats with
    | [] -> return ([], tt)
    | pat :: pats ->
      let pat_type = Type.Var.create ~id_source:(Env.id_source env) () in
      let%bind () = perform_exists pat_type in
      let%bind cpat = infer_pat ~env pat pat_type in
      let%map pat_types, cpats = infer_pats ~env pats in
      pat_type :: pat_types, cpat >> cpats

  and infer_label_pats ~env ~record_type label_pats =
    let open With_fragment in
    label_pats
    |> List.map ~f:(fun (label_name, arg_pat) ->
      infer_label_pat ~env ~label_type:record_type label_name arg_pat)
    |> all
    >>| fun constraints -> Constraint.map (Constraint.all constraints) ~f:ignore

  and infer_label_pat ~env ~label_type label_name arg_pat
    : unit Constraint.t With_fragment.t
    =
    let open With_fragment in
    inst_label ~env ~label_name ~label_type
    @@ fun arg_type -> infer_pat ~env arg_pat arg_type
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

  let inst_constr ~env ~constr_name ~constr_arity ~constr_type k =
    let constr_arg, c_type = inst_constr ~env ~constr_name ~constr_arity ~constr_type in
    let c_arg = k constr_arg in
    let c = c_type >> c_arg in
    Option.value_map constr_arg ~default:c ~f:(fun constr_arg -> exists constr_arg c)
  ;;

  let inst_label ~env ~label_name ~label_type k =
    let label_arg, c_type = inst_label ~env ~label_name ~label_type in
    let c_arg = k label_arg in
    exists label_arg (c_type >> c_arg)
  ;;

  let type_of_matchee : Type.Matchee.t -> Type.t =
    let open Type in
    function
    | Arrow (var1, var2) -> var var1 @-> var var2
    | Constr (args, ident) -> constr (List.map args ~f:var) ident
    | Tuple comps -> tuple (List.map comps ~f:var)
    | Scheme scm -> scheme scm
    | Poly scm -> poly scm
  ;;

  let match_scheme_type ~range scheme_type ~closure ~with_ =
    match_
      scheme_type
      ~closure
      ~with_:(function
        | Scheme { quantifiers; body } -> with_ quantifiers body
        | (Arrow _ | Constr _ | Tuple _ | Poly _) as matchee ->
          with_ [] (type_of_matchee matchee))
      ~error:(fun _ -> Omniml_error.ambiguous_polytype ~range)
      ~default:(fun () -> Constraint (with_ [] (Type.var scheme_type)))
  ;;

  let match_poly_type ~id_source ~range poly_type ~closure ~with_ =
    match_
      poly_type
      ~closure
      ~with_:(function
        | Poly scheme -> with_ scheme
        | (Arrow _ | Constr _ | Tuple _ | Scheme _) as matchee ->
          let type_head =
            match matchee with
            | Arrow _ -> `Arrow
            | Constr _ -> `Constr
            | Tuple _ -> `Tuple
            | Scheme _ -> `Poly
            | _ -> assert false
          in
          ff (Omniml_error.polytype_mismatched_type ~range ~type_head))
      ~error:(fun _ -> Omniml_error.ambiguous_polytype ~range)
      ~default:(fun () ->
        let mono = Type.Var.create ~id_source () in
        Shape (Principal_shape.poly Type.(Scheme.create (var mono))))
  ;;

  let match_inst ~range ~scheme_type ~mono_type =
    match_scheme_type
      ~range
      scheme_type
      ~closure:[ `Type mono_type ]
      ~with_:(fun quantifiers body ->
        exists_many quantifiers Type.(var mono_type =~ body))
  ;;

  let match_scheme ~range cvar ~scheme_type =
    match_scheme_type
      ~range
      scheme_type
      ~closure:[ `Scheme cvar ]
      ~with_:(fun quantifiers body -> forall quantifiers @@ inst cvar body)
  ;;

  let match_poly_inst ~id_source ~range ~poly_type ~mono_type =
    match_poly_type
      ~id_source
      ~range
      poly_type
      ~closure:[ `Type mono_type ]
      ~with_:(fun { quantifiers; body } ->
        exists_many quantifiers Type.(var mono_type =~ body))
  ;;

  let match_poly ~id_source ~range cvar ~poly_type =
    match_poly_type
      ~id_source
      ~range
      poly_type
      ~closure:[ `Scheme cvar ]
      ~with_:(fun { quantifiers; body } -> forall quantifiers @@ inst cvar body)
  ;;

  let infer_pat ~env pat pat_type =
    let { Pattern.Fragment.var_bindings; exist_bindings }, cpat =
      Pattern.(infer_pat ~env pat pat_type |> With_fragment.run)
    in
    let env, named_bindings =
      Map.to_alist var_bindings
      |> List.fold_map ~init:env ~f:(fun env (var, type_) ->
        Env.rename_var env ~var ~in_:(fun env cvar ->
          env, (var, cvar @: Type.var type_.it)))
    in
    env, named_bindings, exist_bindings, cpat
  ;;

  let bind_mono_pat ~env (pat : pattern) pat_type ~in_ =
    let env, named_bindings, exists_bindings, cpat = infer_pat ~env pat pat_type in
    let bindings = List.map named_bindings ~f:snd in
    let in_ = in_ env in
    exists_many exists_bindings (cpat >> let_unit (mono_binding bindings) ~in_)
  ;;

  let bind_mono_match_val ~env pat param_type ~in_ =
    let id_source = Env.id_source env in
    exists' ~id_source
    @@ fun param_mono_type ->
    Type.(var param_type =~ scheme (Type.Scheme.create (var param_mono_type)))
    >> bind_mono_pat ~env pat param_mono_type ~in_
  ;;

  let bind_unknown_poly_pat ~env (pat : Ast.pattern) param_type ~in_ =
    let id_source = Env.id_source env in
    let pat_type = Type.Var.create ~id_source () in
    let env, named_bindings, exist_bindings, cpat = infer_pat ~env pat pat_type in
    let bindings = List.map named_bindings ~f:snd in
    let pat_quantifiers = List.map exist_bindings ~f:(fun v -> Flexible, v) in
    let_unit
      (poly_binding
         (((Flexible, pat_type) :: pat_quantifiers)
          @. (match_inst ~range:pat.range ~scheme_type:param_type ~mono_type:pat_type
              >> cpat)
          @=> bindings))
      ~in_:(in_ env)
  ;;

  let bind_known_poly_pat ~env pat scheme param_type ~in_ =
    let id_source = Env.id_source env in
    let scm = Convert.core_scheme_to_type_scheme ~env scheme in
    let scheme_quantifiers = List.map scm.quantifiers ~f:(fun v -> Rigid, v) in
    (* Infer the pattern *)
    let pat_type = Type.Var.create ~id_source () in
    let env, named_bindings, exist_bindings, cpat = infer_pat ~env pat pat_type in
    let bindings = List.map named_bindings ~f:snd in
    let pat_quantifiers =
      (Flexible, pat_type) :: List.map exist_bindings ~f:(fun v -> Flexible, v)
    in
    (* Unify the parameter type with the expected scheme type. *)
    Type.(var param_type =~ scheme scm)
    >> let_unit
         (poly_binding
            ((scheme_quantifiers @ pat_quantifiers)
             @. (cpat >> Type.(var pat_type =~ scm.body))
             @=> bindings))
         ~in_:(in_ env)
  ;;

  let bind_param ~env param type_ ~in_ =
    match With_range.it param with
    | Param_mono_val pat ->
      if Omniml_options.is_enabled (Env.options env) First_class_polymorphism
      then bind_unknown_poly_pat ~env pat type_ ~in_
      else bind_mono_pat ~env pat type_ ~in_
    | Param_poly_val { pat; scheme } ->
      assert_with_fcp ~env ~range:param.range;
      bind_known_poly_pat ~env pat scheme type_ ~in_
  ;;

  let rec bind_params ~env params_and_types ~in_ =
    match params_and_types with
    | [] -> in_ env
    | (param, param_type) :: params_and_types ->
      bind_param ~env param param_type ~in_:(fun env ->
        bind_params ~env params_and_types ~in_)
  ;;

  let rec infer_exp ~(env : Env.t) (exp : expression) (exp_type : Type.Var.t) =
    let id_source = Env.id_source env in
    with_range ~range:exp.range
    @@
    match exp.it with
    | Exp_var var ->
      (match Env.find_var env var.it with
       | Some var -> inst var (Type.var exp_type)
       | None -> Omniml_error.(raise @@ unbound_variable ~range:var.range var.it))
    | Exp_const const -> Type.(var exp_type =~ infer_constant const)
    | Exp_fun (params, ret_type_annot, exp_body) ->
      let ret_type_annot =
        Option.map ret_type_annot ~f:(Convert.core_type_to_type ~env)
      in
      let infer_arrow ~range ~env ~param ?expected_ret_type arr_type ~infer_body =
        exists' ~id_source
        @@ fun scheme_param_type ->
        exists' ~id_source
        @@ fun scheme_ret_type ->
        (* Ensure [arr_type] is an arrow with parameter type [scheme_param_type]
           and return type [scheme_ret_type]. *)
        Type.(var arr_type =~ var scheme_param_type @-> var scheme_ret_type)
        (* Check the expected ret type *)
        >> Option.value_map expected_ret_type ~default:tt ~f:(fun expected_ret_type ->
          Type.(var scheme_ret_type =~ expected_ret_type))
        >> bind_param ~env param scheme_param_type ~in_:(fun env ->
          (* Check that [exp] has a more general type than [scheme_ret_type]. *)
          if Omniml_options.is_enabled (Env.options env) First_class_polymorphism
          then
            with_range ~range
            @@ infer_principal ~env ~f:(fun body_type -> infer_body ~env body_type)
            @@ fun cvar -> match_scheme ~range cvar ~scheme_type:scheme_ret_type
          else infer_body ~env scheme_ret_type)
      in
      let rec infer_arrows ~env params arr_type =
        match params with
        | [] -> assert false
        | [ param ] ->
          infer_arrow
            ~range:exp_body.range
            ~env
            ~param
            ?expected_ret_type:ret_type_annot
            arr_type
            ~infer_body:(fun ~env exp_type -> infer_exp ~env exp_body exp_type)
        | param :: params ->
          infer_arrow
            ~range:exp.range
            ~env
            ~param
            arr_type
            ~infer_body:(fun ~env arr_type -> infer_arrows ~env params arr_type)
      in
      infer_arrows ~env params exp_type
    | Exp_app (exp1, exp2) ->
      exists' ~id_source
      @@ fun arr_type ->
      exists' ~id_source
      @@ fun scheme_param_type ->
      exists' ~id_source
      @@ fun scheme_ret_type ->
      (* Ensure that [exp1] has an arrow with parameter type [scheme_param_type]
         and return type [scheme_ret_type]. *)
      let c1 =
        infer_exp ~env exp1 arr_type
        >> with_range ~range:exp1.range
           @@ Type.(var arr_type =~ var scheme_param_type @-> var scheme_ret_type)
      in
      (* Check that [exp2] has a more general type than [scheme_param_type]. *)
      let c2 =
        if Omniml_options.is_enabled (Env.options env) First_class_polymorphism
        then
          infer_exp_principal ~env exp2
          @@ fun cvar ->
          match_scheme ~range:exp2.range cvar ~scheme_type:scheme_param_type
        else infer_exp ~env exp2 scheme_param_type
      in
      c1
      >> c2
      >>
      (* Check that [exp_type] is an instance of [scheme_ret_type]. *)
      if Omniml_options.is_enabled (Env.options env) First_class_polymorphism
      then match_inst ~range:exp.range ~scheme_type:scheme_ret_type ~mono_type:exp_type
      else Type.(var scheme_ret_type =~ var exp_type)
    | Exp_let (value_binding, exp) ->
      (infer_value_binding ~env value_binding @@ fun env -> infer_exp ~env exp exp_type)
      >>| ignore
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
      let_unit
        (poly_binding
           (((Flexible, exp_type') :: rigid_type_vars)
            @. c
            @=> [ x @: Type.var exp_type' ]))
        ~in_:(inst x (Type.var exp_type))
    | Exp_annot (exp, annot) ->
      let annot = Convert.core_type_to_type ~env annot in
      let c = infer_exp ~env exp exp_type in
      Type.(var exp_type =~ annot) >> c
    | Exp_tuple exps ->
      infer_exps ~env exps
      @@ fun (exp_types, c) ->
      Type.(var exp_type =~ tuple (List.map ~f:var exp_types)) >> c
    | Exp_proj (exp', index) ->
      exists' ~id_source
      @@ fun tuple_type ->
      let c1 = infer_exp ~env exp' tuple_type in
      c1
      >> match_
           tuple_type
           ~closure:[ `Type exp_type ]
           ~with_:(function
             | Tuple comp_types ->
               (match List.nth comp_types (index - 1) with
                | None ->
                  let arity = List.length comp_types in
                  ff
                    (Omniml_error.projection_out_of_bounds ~range:exp.range ~index ~arity)
                | Some comp_type -> Type.(var exp_type =~ var comp_type))
             | (Arrow _ | Constr _ | Scheme _ | Poly _) as matchee ->
               let type_head =
                 match matchee with
                 | Arrow _ -> `Arrow
                 | Constr _ -> `Constr
                 | Scheme _ | Poly _ -> `Poly
                 | _ -> assert false
               in
               ff
                 (Omniml_error.disambiguation_tuple_mismatched_type
                    ~range:exp.range
                    ~type_head))
           ~error:(fun _ -> Omniml_error.ambiguous_tuple ~range:exp.range)
           ~default:(fun () -> Shape (Principal_shape.tuple (Int.max index 2)))
    | Exp_if_then_else (if_exp, then_exp, else_exp) ->
      exists' ~id_source
      @@ fun if_type ->
      let c1 = infer_exp ~env if_exp if_type in
      let c2 = infer_exp ~env then_exp exp_type in
      let c3 = infer_exp ~env else_exp exp_type in
      Type.(var if_type =~ Predef.bool) >> c1 >> c2 >> c3
    | Exp_sequence (exp1, exp2) ->
      exists' ~id_source
      @@ fun exp1_type ->
      let c1 = infer_exp ~env exp1 exp1_type in
      let c2 = infer_exp ~env exp2 exp_type in
      Type.(var exp1_type =~ Predef.unit) >> c1 >> c2
    | Exp_constr (constr_name, arg_exp) ->
      inst_constr
        ~env
        ~constr_name
        ~constr_arity:(infer_constructor_arity ~constr_name arg_exp)
        ~constr_type:exp_type
      @@ fun arg_type ->
      (match arg_exp, arg_type with
       | Some arg_exp, Some arg_type -> infer_exp ~env arg_exp arg_type
       | None, None -> tt
       | _ ->
         Omniml_error.(
           raise
           @@ bug_s
                ~here:[%here]
                [%message
                  "Constructor argument mistmatch in expression" (exp : Ast.expression)]))
    | Exp_match (match_exp, cases) ->
      exists' ~id_source
      @@ fun match_exp_type ->
      let c1 = infer_exp ~env match_exp match_exp_type in
      let c2 = infer_cases ~env cases ~lhs_type:match_exp_type ~rhs_type:exp_type in
      c1 >> c2
    | Exp_record label_exps -> infer_label_exps ~env ~record_type:exp_type label_exps
    | Exp_field (exp, label_name) ->
      exists' ~id_source
      @@ fun record_type ->
      let c1 = infer_exp ~env exp record_type in
      let c2 =
        inst_label ~env ~label_name ~label_type:record_type
        @@ fun arg_type -> Type.(var exp_type =~ var arg_type)
      in
      c1 >> c2
    | Exp_poly (exp, scheme_annot) ->
      (match scheme_annot with
       | None ->
         infer_exp_principal ~env exp
         @@ fun cvar -> match_poly ~id_source ~range:exp.range cvar ~poly_type:exp_type
       | Some core_scheme ->
         let scheme' = Convert.core_scheme_to_type_scheme ~env core_scheme in
         Type.(var exp_type =~ poly scheme')
         >> forall scheme'.quantifiers
            @@ exists' ~id_source
            @@ fun exp_type ->
            Type.(var exp_type =~ scheme'.body) >> infer_exp ~env exp exp_type)
    | Exp_inst exp ->
      exists' ~id_source
      @@ fun poly_type ->
      infer_exp ~env exp poly_type
      >> match_poly_inst ~id_source ~range:exp.range ~poly_type ~mono_type:exp_type

  and infer_exps ~env exps k =
    match exps with
    | [] -> k ([], tt)
    | exp :: exps ->
      exists' ~id_source:(Env.id_source env)
      @@ fun exp_type ->
      let c1 = infer_exp ~env exp exp_type in
      infer_exps ~env exps @@ fun (exp_types, c2) -> k (exp_type :: exp_types, c1 >> c2)

  and infer_label_exps ~env ~record_type label_exps =
    label_exps
    |> List.map ~f:(fun (label_name, arg_exp) ->
      infer_label_exp ~env ~label_type:record_type label_name arg_exp)
    |> all
    >>| ignore

  and infer_label_exp ~env ~label_type label_name arg_exp =
    inst_label ~env ~label_name ~label_type
    @@ fun arg_type -> infer_exp ~env arg_exp arg_type

  and infer_principal ~env ~f k =
    let id_source = Env.id_source env in
    let cvar = Var.create ~id_source () in
    let type_ = Type.Var.create ~id_source () in
    let_unit
      (poly_binding ([ Flexible, type_ ] @. f type_ @=> [ cvar @: Type.var type_ ]))
      ~in_:(k cvar)

  and infer_exp_principal ~env exp k =
    with_range ~range:exp.range @@ infer_principal ~env ~f:(infer_exp ~env exp) k

  and infer_cases ~env cases ~lhs_type ~rhs_type =
    let cs = cases |> List.map ~f:(infer_case ~env ~lhs_type ~rhs_type) in
    all cs >>| ignore

  and infer_case ~env case ~lhs_type ~rhs_type =
    let { case_lhs = pat; case_rhs = exp } = case.it in
    bind_mono_pat ~env pat lhs_type ~in_:(fun env -> infer_exp ~env exp rhs_type)

  and infer_value_binding
    :  'a.
       env:Env.t
    -> Ast.value_binding
    -> (Env.t -> 'a Constraint.t)
    -> (Typed_ast.binding list * 'a) Constraint.t
    =
    fun ~env value_binding k ->
    let { value_binding_pat = pat; value_binding_exp = exp } = value_binding.it in
    let exp_type = Type.Var.create ~id_source:(Env.id_source env) () in
    let cexp = infer_exp ~env exp exp_type in
    let env, named_bindings, exists_bindings, cpat = infer_pat ~env pat exp_type in
    let bindings = List.map named_bindings ~f:snd in
    let decoded_bindings =
      named_bindings
      |> List.map ~f:(fun (binding_name, binding) ->
        decode binding.binding_type
        >>| fun binding_type -> { Typed_ast.binding_name; binding_type })
      |> all
    in
    let cin = k env in
    let_
      (poly_binding
         (((Flexible, exp_type) :: List.map exists_bindings ~f:(fun v -> Flexible, v))
          @. (cexp >> cpat >> decoded_bindings)
          @=> bindings))
      ~in_:cin
  ;;
end

module Structure = struct
  let infer_prim ~env (value_desc : value_description) k =
    let { value_type; value_name } = value_desc.it in
    let scheme = Convert.core_scheme_to_type_scheme ~env value_type in
    let quantifiers = List.map ~f:(fun q -> Flexible, q) scheme.quantifiers in
    Env.rename_var env ~var:value_name.it ~in_:(fun env cvar ->
      let binding = cvar @: scheme.body in
      let decoded_binding =
        decode binding.binding_type
        >>| fun binding_type -> { Typed_ast.binding_name = value_name.it; binding_type }
      in
      let_ (poly_binding (quantifiers @. decoded_binding @=> [ binding ])) ~in_:(k env))
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
      | Type_decl_alias core_type ->
        Adt.Type_alias
          { alias_alphas = List.map type_decl_params ~f:With_range.it
          ; alias_type = core_type
          }
      | Type_decl_variant constr_decls ->
        let constructor_type =
          Adt.Type_constr
            ( List.map type_decl_params ~f:(fun type_var -> Adt.Type_var type_var.it)
            , type_ident )
        in
        let constr_decls =
          List.map constr_decls ~f:(fun { constructor_name; constructor_arg } ->
            let constructor_arg =
              Option.map constructor_arg ~f:(Convert.core_type_to_type_expr ~env)
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
            let label_arg = Convert.core_type_to_type_expr ~env label_arg in
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
    | [] -> return []
    | { it = Str_type type_decls; range } :: str ->
      let env = infer_type_decls ~env type_decls in
      with_range ~range
      @@ (infer_str ~env str
          >>| fun signature ->
          With_range.create ~range (Typed_ast.Sig_type type_decls) :: signature)
    | { it = Str_primitive value_desc; range } :: str ->
      (with_range ~range @@ infer_prim ~env value_desc @@ fun env -> infer_str ~env str)
      >>| fun (binding, signature) ->
      With_range.create ~range (Typed_ast.Sig_primitive binding) :: signature
    | { it = Str_value value_binding; range } :: str ->
      (with_range ~range
       @@ Expression.infer_value_binding ~env value_binding
       @@ fun env -> infer_str ~env str)
      >>| fun (bindings, signature) ->
      With_range.create ~range (Typed_ast.Sig_value bindings) :: signature
  ;;
end
