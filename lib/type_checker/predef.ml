open! Import
open Constraint
open Ast_types

(* Pre-defined types have their own [id_source] since the type names cannot be parsed => no conflict possible *)
let id_source = Identifier.create_source ()
let int_ident = Type.Ident.create ~id_source ~name:"Stdlib.int" ()
let bool_ident = Type.Ident.create ~id_source ~name:"Stdlib.bool" ()
let unit_ident = Type.Ident.create ~id_source ~name:"Stdlib.unit" ()
let int = Type.(constr [] int_ident)
let bool = Type.(constr [] bool_ident)
let unit = Type.(constr [] unit_ident)

module Env = struct
  let arg_type ~with_fcp:_ type_ = type_
  let ret_type ~with_fcp:_ type_ = type_

  let bool_bop ~with_fcp =
    Type.(
      arg_type ~with_fcp bool
      @-> ret_type ~with_fcp (arg_type ~with_fcp bool @-> ret_type ~with_fcp bool))
  ;;

  let bool_uop ~with_fcp = Type.(arg_type ~with_fcp bool @-> ret_type ~with_fcp bool)

  let int_bop ~with_fcp =
    Type.(
      arg_type ~with_fcp int
      @-> ret_type ~with_fcp (arg_type ~with_fcp int @-> ret_type ~with_fcp int))
  ;;

  let int_uop ~with_fcp = Type.(arg_type ~with_fcp int @-> ret_type ~with_fcp int)

  let int_comparator ~with_fcp =
    Type.(
      arg_type ~with_fcp int
      @-> ret_type ~with_fcp (arg_type ~with_fcp int @-> ret_type ~with_fcp bool))
  ;;

  let type_def name arity ident =
    { Adt.type_name = Type_name.create name
    ; type_arity = arity
    ; type_ident = ident
    ; type_kind = Type_abstract
    }
  ;;

  let t = [ "int", 0, int_ident; "bool", 0, bool_ident; "unit", 0, unit_ident ]

  let v ~with_fcp =
    [ "( || )", bool_bop ~with_fcp
    ; "( && )", bool_bop ~with_fcp
    ; "not", bool_uop ~with_fcp
    ; "( = )", int_comparator ~with_fcp
    ; "( <> )", int_comparator ~with_fcp
    ; "( < )", int_comparator ~with_fcp
    ; "( > )", int_comparator ~with_fcp
    ; "( <= )", int_comparator ~with_fcp
    ; "( >= )", int_comparator ~with_fcp
    ; "( + )", int_bop ~with_fcp
    ; "( - )", int_bop ~with_fcp
    ; "( * )", int_bop ~with_fcp
    ; "( / )", int_bop ~with_fcp
    ; "unary( - )", int_uop ~with_fcp
    ]
  ;;

  let init () =
    let env = Env.empty () in
    let env =
      List.fold t ~init:env ~f:(fun env (type_str, type_arity, type_ident) ->
        Env.add_type_def env (type_def type_str type_arity type_ident))
    in
    env
  ;;

  let wrap ~with_fcp k =
    let env = init () in
    let env, bindings =
      List.fold_map (v ~with_fcp) ~init:env ~f:(fun env (var_str, type_) ->
        Env.rename_var env ~var:(Var_name.create var_str) ~in_:(fun env cvar ->
          env, (cvar, type_)))
    in
    let c = k env in
    let_ (mono_binding (List.map bindings ~f:(fun (var, type_) -> var @: type_))) ~in_:c
    >>| snd
  ;;
end
