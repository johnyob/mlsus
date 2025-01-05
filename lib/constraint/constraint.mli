open Core
open Mlsus_std

(** The module [Type] provides the concrete representation of types
    (using constraint type variables) in constraints. *)
module Type : sig
  module Ident : Var.S
  module Var : Var.S

  module Matchee : sig
    (** [t] is a matchee, a partial (shallow) type that is matched on. *)
    type t =
      | Arrow of Var.t * Var.t
      | Tuple of Var.t list
      | Constr of Var.t list * Ident.t
    [@@deriving sexp]
  end

  (** [t] represents the type [tau]. *)
  type t =
    | Arrow of t * t (** [tau -> tau] *)
    | Tuple of t list (** [tau1 * ... * taun] *)
    | Constr of t list * Ident.t (** [(tau1, ..., taun) F] *)
    | Var of Var.t (** [ɑ] *)
  [@@deriving sexp]

  val var : Var.t -> t
  val ( @-> ) : t -> t -> t
  val constr : t list -> Ident.t -> t
  val tuple : t list -> t
end

module Var : Var.S

module Closure : sig
  type t = { type_vars : Type.Var.Set.t } [@@unboxed] [@@deriving sexp]
end

(** [t] is a constraint *)
type t =
  | True (** [true] *)
  | False of Error.t (** [false] *)
  | Conj of t * t (** [C1 /\ C2] *)
  | Eq of Type.t * Type.t (** [tau1 = tau2] *)
  | Exists of Type.Var.t * t (** [exists overline(a). C]*)
  | Let of Var.t * scheme * t (** [let x = sigma in C] *)
  | Instance of Var.t * Type.t (** [x <= tau] *)
  | Match of Type.Var.t * Closure.t * (Type.Matchee.t -> t)
  (** [match a with [overline(a)]f] *)

(** [scheme] is a constrainted type scheme [overline(a). C => tau] *)
and scheme =
  { type_vars : Type.Var.t list
  ; in_ : t
  ; type_ : Type.t
  }
[@@deriving sexp]

val tt : t
val ff : Error.t -> t
val ( &~ ) : t -> t -> t
val all : t list -> t
val ( =~ ) : Type.t -> Type.t -> t
val exists : Type.Var.t -> t -> t
val exists_many : Type.Var.t list -> t -> t
val ( #= ) : Var.t -> scheme -> Var.t * scheme

type unquantified_scheme := t * Type.t
type quantified_scheme := Type.Var.t list * unquantified_scheme

val ( @=> ) : t -> Type.t -> unquantified_scheme
val ( @. ) : Type.Var.t list -> unquantified_scheme -> quantified_scheme
val mono_scheme : Type.t -> scheme
val poly_scheme : quantified_scheme -> scheme
val let_ : Var.t * scheme -> in_:t -> t
val inst : Var.t -> Type.t -> t
val match_ : Type.Var.t -> closure:Type.Var.t list -> with_:(Type.Matchee.t -> t) -> t
