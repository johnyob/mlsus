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
