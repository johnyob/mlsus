open! Import

(** [infer_exp exp] returns the constraint generated by [exists 'a. [| exp : 'a |]]. *)
val infer_exp : Ast.expression -> Constraint.t Or_error.t

(** [infer_str str] returns the constraint generated by [[| str |]] *)
val infer_str : Ast.structure -> Constraint.t Or_error.t

(** A module containing functions exposed for unit tests *)
module Private : sig
  module Env = Env
  module Adt = Adt
  module Predef = Predef

  type 'a infer_with_env_transformer :=
    ?env_xfmr:(Env.t -> Env.t) -> 'a -> Constraint.t Or_error.t

  val infer_exp : Ast.expression infer_with_env_transformer
  val infer_str : Ast.structure infer_with_env_transformer
end