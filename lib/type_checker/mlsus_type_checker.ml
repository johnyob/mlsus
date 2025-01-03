open! Import
open Constraint

let infer_exp_with_env_transformer ?(env_xfmr = Fn.id) exp =
  Predef.Env.wrap
  @@ fun env ->
  let open Or_error.Let_syntax in
  let exp_type = Type.Var.create ~id_source:(Env.id_source env) ~name:"exp_type0" () in
  let%map c = Infer.Expression.infer_exp ~env:(env_xfmr env) exp (Type.var exp_type) in
  exists exp_type c
;;

let infer_str_with_env_transformer ?(env_xfmr = Fn.id) str =
  Predef.Env.wrap @@ fun env -> Infer.Structure.infer_str ~env:(env_xfmr env) str
;;

let infer_exp exp = infer_exp_with_env_transformer exp
let infer_str str = infer_str_with_env_transformer str

module Private = struct
  module Env = Env
  module Adt = Adt
  module Predef = Predef

  let infer_exp = infer_exp_with_env_transformer
  let infer_str = infer_str_with_env_transformer
end
