open Core
open Mlsus_std
open Grace

(** The module [Type] provides the concrete representation of types
    (using constraint type variables) in constraints. *)
module rec Type : sig
  module Ident : Var.S
  module Var : Var.S

  (** [t] represents the type [tau]. *)
  type t =
    | Var of Var.t (** Type variable ['a] *)
    | Arrow of t * t (** Function types [tua1 -> tau2] *)
    | Tuple of t list (** Tuple types [tau1 * ... * taun] *)
    | Constr of t list * Ident.t (** Nominal types [(tau1, ..., taun) T] *)
    | Shape of t list * Principal_shape.t (** Applied shape [(tau1, ..., taun) s] *)
    | Poly of Type_scheme.t (** Polytypes [[sigma]] *)
  [@@deriving sexp, equal, compare, hash]

  val var : Var.t -> t
  val ( @-> ) : t -> t -> t
  val constr : t list -> Ident.t -> t
  val tuple : t list -> t
  val shape : t list -> Principal_shape.t -> t
  val poly : Type_scheme.t -> t

  module Matchee : sig
    (** [t] is a matchee, a principal shape of the type being matched. 
        The shape quantifiers are implicitly bound. *)
    type t =
      | Arrow of Var.t * Var.t
      | Tuple of Var.t list
      | Constr of Var.t list * Ident.t
      | Poly of Type_scheme.t
    [@@deriving sexp]
  end
end

and Type_scheme : sig
  (** [t] represents a polymorphic type [forall 'a1, ..., 'an. tau] *)
  type t =
    { quantifiers : Type.Var.t list
    ; body : Type.t
    }
  [@@deriving sexp, equal, compare, hash]

  val create : ?quantifiers:Type.Var.t list -> Type.t -> t
end

and Principal_shape : sig
  module Poly : sig
    type t = private
      { quantifiers : Type.Var.t list
      ; scheme : Type_scheme.t
      }
    [@@deriving sexp, equal, compare, hash]

    include Invariant.S with type t := t

    val create : ?quantifiers:Type.Var.t list -> Type_scheme.t -> t

    val create_unchecked : ?quantifiers:Type.Var.t list -> Type_scheme.t -> t
    [@@alert
      unsafe "Safety: this function does not guarantee that the poly shape is principal"]
  end

  type t =
    | Sh_arrow (** Arrow shape ['c1 'c2. 'c1 -> 'c2] *)
    | Sh_tuple of int (** Tuple shape ['c1, ..., 'cn. 'c1 * ... * 'cn] *)
    | Sh_constr of int * Type.Ident.t
    (** Nominal type shape ['c1, ..., 'cn. ('c1, ..., 'cn) T] *)
    | Sh_poly of Poly.t (** Polytype shape ['c1, ..., 'cn. [sigma]] *)
  [@@deriving sexp, equal, compare, hash]
end

module Var : Var.S

module Closure : sig
  type t =
    { type_vars : Type.Var.t list
    ; vars : Var.t list
    }
  [@@deriving sexp]
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
  -> closure:[< `Type of Type.Var.t | `Scheme of Var.t ] list
  -> with_:(Type.Matchee.t -> t)
  -> else_:(unit -> t)
  -> t

val with_range : t -> range:Range.t -> t

module Quickcheckable : sig
  module Type : Quickcheckable.S with type t := Type.t
  module Type_scheme : Quickcheckable.S with type t := Type_scheme.t
  module Principal_shape : Quickcheckable.S with type t := Principal_shape.t
end
