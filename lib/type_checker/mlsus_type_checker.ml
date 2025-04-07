open! Import
open Constraint

let empty_env_wrapper f = f (Env.empty ())

let stdlib_wrapper ?(with_stdlib = true) f =
  if with_stdlib then Predef.Env.wrap f else empty_env_wrapper f
;;

let infer_exp ?with_stdlib exp =
  stdlib_wrapper ?with_stdlib
  @@ fun env ->
  let exp_type = Type.Var.create ~id_source:(Env.id_source env) ~name:"exp_type0" () in
  let c = Infer.Expression.infer_exp ~env exp (Type.var exp_type) in
  exists exp_type c
;;

let infer_str ?with_stdlib str =
  stdlib_wrapper ?with_stdlib @@ fun env -> Infer.Structure.infer_str ~env str
;;

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
     | Cannot_resume_suspended_generic errs | Cannot_resume_match_due_to_cycle errs ->
       (* FIXME: We don't have a way to compose many errors into one, so we just pick one for now :/ *)
       Mlsus_error.raise @@ List.hd_exn errs)
;;
