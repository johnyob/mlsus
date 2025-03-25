open! Import
module G := Generalization
module Var : Var.S
module Ident = Constraint.Type.Ident

type t =
  | Var of Var.t
  | Arrow of t * t
  | Tuple of t list
  | Constr of t list * Ident.t
  | Mu of Var.t * t
[@@deriving sexp]

include Pretty_printer.S with type t := t

module Decoder : sig
  (** A decoder is a function that converts a (graphical) type into a decoded type *)
  type nonrec t = G.Type.t -> t

  (** [create ()] returns a fresh decoder.

      All decoded types will share a common identifier source and coherent set of variable
      renamings. *)
  val create : unit -> t
end
