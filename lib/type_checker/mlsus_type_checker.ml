open! Import
open Constraint

let infer_exp exp =
  Predef.Env.wrap
  @@ fun env ->
  let exp_type = Type.Var.create ~id_source:(Env.id_source env) ~name:"exp_type0" () in
  let c = Infer.Expression.infer_exp ~env exp (Type.var exp_type) in
  exists exp_type c
;;

let infer_str str = Predef.Env.wrap @@ fun env -> Infer.Structure.infer_str ~env str

let check cst =
  match Mlsus_constraint_solver.solve cst with
  | Ok () -> ()
  | Error { range; it } ->
    let get_range range =
      Option.value_or_thunk range ~default:(fun () ->
        Mlsus_error.(
          raise
          @@ bug_s
               ~here:[%here]
               [%message
                 "Expect range to be given"
                   (it : Mlsus_constraint_solver.Error.desc)
                   (cst : Constraint.t)]))
    in
    (match it with
     | Unsatisfiable err -> Mlsus_error.raise err
     | Unbound_type_var type_var ->
       Mlsus_error.(
         raise
         @@ bug_s
              ~here:[%here]
              [%message
                "Unbound constraint type variable"
                  (type_var : Constraint.Type.Var.t)
                  (range : Range.t option)
                  (cst : Constraint.t)])
     | Unbound_var var ->
       Mlsus_error.(
         raise
         @@ bug_s
              ~here:[%here]
              [%message
                "Unbound constraint variable"
                  (var : Constraint.Var.t)
                  (range : Range.t option)
                  (cst : Constraint.t)])
     | Cannot_unify (type1, type2) ->
       Mlsus_error.(
         raise
         @@ mismatched_type
              ~range:(get_range range)
              ~pp_type:Mlsus_constraint_solver.Decoded_type.pp
              type1
              type2)
     (* FIXME: These errors should be better, but the solver doesn't provide enough information to
       give an informative error *)
     | Cannot_resume_match_due_to_cycle ->
       Mlsus_error.(
         raise @@ bug_s ~here:[%here] [%message "Cannot resume match due to cycle"])
     | Cannot_resume_suspended_generic ->
       Mlsus_error.(
         raise @@ bug_s ~here:[%here] [%message "Cannot resume suspended generic"]))
;;
