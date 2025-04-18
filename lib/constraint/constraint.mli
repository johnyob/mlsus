open Core
open Mlsus_std
open Grace

(** The module [Type] provides the concrete representation of types
    (using constraint type variables) in constraints. *)
module Type : sig
  module Ident : Var.S
  module Var : Var.S

  module Head : sig
    (** [t] is the head of a type *)
    type t =
      | Arrow
      | Tuple of int
      | Constr of Ident.t
    [@@deriving sexp]

    include Comparable.S with type t := t
  end

  module Matchee : sig
    (** [t] is a matchee, a partial (shallow) type that is matched on. *)
    type t =
      | App of Var.t * Var.t
      | Head of Head.t
      | Spine of Var.t list
      | Rigid_var
    [@@deriving sexp]
  end

  (** [t] represents the type [tau]. *)
  type t =
    | Head of Head.t (** [F] *)
    | App of t * t (** [tau1 tau2] where [tau1] is a spine and [tau2] is a head *)
    | Spine of t list (** [(tau1, ..., taun)] is a spine *)
    | Var of Var.t (** [ɑ] *)
  [@@deriving sexp]

  val var : Var.t -> t
  val ( @-> ) : t -> t -> t
  val constr : t list -> Ident.t -> t
  val tuple : t list -> t
  val spine : t list -> t
  val ( @% ) : t -> t -> t
end

module Var : Var.S

module Closure : sig
  type t = { type_vars : Type.Var.Set.t } [@@unboxed] [@@deriving sexp]
end

(** [t] is a constraint *)
type t =
  | True (** [true] *)
  | False of Mlsus_error.t (** [false] *)
  | Conj of t * t (** [C1 /\ C2] *)
  | Eq of Type.t * Type.t (** [tau1 = tau2] *)
  | Exists of Type.Var.t * t (** [exists overline(a). C]*)
  | Let of Var.t * scheme * t (** [let x = sigma in C] *)
  | Instance of Var.t * Type.t (** [x <= tau] *)
  | Match of
      { matchee : Type.Var.t
      ; closure : Closure.t
      ; case : Type.Matchee.t -> t
      ; else_ : unit -> t
      } (** [match a with [overline(a)]f] else default *)
  | With_range of t * Range.t (** [C^ell] *)

(** [scheme] is a constrainted type scheme [overline(a). C => tau] *)
and scheme =
  { type_vars : (flexibility * Type.Var.t) list
  ; in_ : t
  ; type_ : Type.t
  }

and flexibility =
  | Flexible
  | Rigid
[@@deriving sexp]

val tt : t
val ff : Mlsus_error.t -> t
val ( &~ ) : t -> t -> t
val all : t list -> t
val ( =~ ) : Type.t -> Type.t -> t
val exists : Type.Var.t -> t -> t
val exists_many : Type.Var.t list -> t -> t
val ( #= ) : Var.t -> scheme -> Var.t * scheme

type unquantified_scheme := t * Type.t
type quantified_scheme := (flexibility * Type.Var.t) list * unquantified_scheme

val ( @=> ) : t -> Type.t -> unquantified_scheme
val ( @. ) : (flexibility * Type.Var.t) list -> unquantified_scheme -> quantified_scheme
val mono_scheme : Type.t -> scheme
val poly_scheme : quantified_scheme -> scheme
val let_ : Var.t * scheme -> in_:t -> t
val inst : Var.t -> Type.t -> t

val match_
  :  Type.Var.t
  -> closure:Type.Var.t list
  -> with_:(Type.Matchee.t -> t)
  -> else_:(unit -> t)
  -> t

val with_range : t -> range:Range.t -> t
