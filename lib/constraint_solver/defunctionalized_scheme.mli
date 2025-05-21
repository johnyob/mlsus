open! Import
open! Constraint

module State : sig
  type t [@@deriving sexp_of]

  val create : unit -> t
end

type t =
  { closure : Type.Var.t list
  ; skeleton : Type.Scheme_skeleton_ident.t
  }
[@@deriving sexp]

val of_constraint_scheme
  :  state:State.t
  -> alloc_skeleton:
       (closure:Type.Var.t list -> scheme:Type.scheme -> Type.Scheme_skeleton_ident.t)
  -> Type.scheme
  -> t
