open Core
open Mlsus_std
open Grace

(** The module [Type] provides the concrete representation of types
    (using constraint type variables) in constraints. *)
module Type : sig
  (** Type identifiers for constructors *)
  module Ident : Var.S

  (** Identifiers for type scheme skeletons *)
  module Scheme_skeleton_ident : Var.S

  (** Variables that represent types ['a] *)
  module Var : Var.S

  module Head : sig
    (** [t] is the head of a type *)
    type t =
      | Arrow
      | Tuple of int
      | Constr of Ident.t
      | Poly
      | Scheme of Scheme_skeleton_ident.t
    [@@deriving equal, compare, hash, sexp]

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

  (** [t] represents a sorted-kinded-type [tau].
  
      Kinds are either [*] (for monotypes) or [scm] (for type schemes), 
      Sorts are [sp] (for spines), [hd] for heads. *)
  type t =
    | Head of Head.t (** [F] *)
    | App of t * t (** [tau1 tau2] where [tau1] is a spine and [tau2] is a head *)
    | Spine of t list (** [(tau1, ..., taun)] is a spine *)
    | Var of Var.t (** ['ɑ] *)
    | Defunctionalized_scheme of scheme (** [D[|sigma|]] of kind [scm] *)

  (** [scheme] represents a polymorphic type. 
  
      Our constraint language exposes a canonical defunctionalized 
      representation of type schemes. 
      
      Namely, a type scheme 
      {v
        forall ('b1, ..., 'bn). tau
      v}
      may be viewed as a function from types to types, with a closure. 

      We expliclity write this as: 
      {v
        ['a1, ..., 'an]forall ('b1, ..., 'bn). tau
      v}
      where the closure ['a1, ..., 'an] is defined as  [fv(tau) \ 'b1, ..., 'bn]. 

      We call the underlying function, the 'skeleton' of the type scheme. 
      Each scheme maps to a canonical skeleton and a closure (applied to the skeleton). 
      These heads may be exposed using suspended constraints (and matching on a scheme head). 
    *)
  and scheme =
    { scheme_quantifiers : Var.t list (** The polymorphic variables of the type scheme. *)
    ; scheme_body : t (** The type of the body *)
    }
  [@@deriving sexp]

  (** [defunctionalized_scheme] represents a defunctionalized [sigma]. *)
  type defunctionalized_scheme =
    { scheme_closure : t (** [closure] of the scheme of sort [sp] *)
    ; scheme_skeleton : Scheme_skeleton_ident.t
    }
  [@@deriving sexp]

  val var : Var.t -> t
  val ( @-> ) : t -> t -> t
  val constr : t list -> Ident.t -> t
  val tuple : t list -> t
  val spine : t list -> t
  val ( @% ) : t -> t -> t
  val hd : Head.t -> t
  val poly : t -> t
  val defunctionalized_scheme : scheme -> t
  val ( @. ) : Var.t list -> t -> scheme
end

module Var : Var.S

module Closure : sig
  type t = { type_vars : Type.Var.t list } [@@unboxed] [@@deriving sexp]
end

(** [t] is a constraint *)
type t =
  | True (** [true] *)
  | False of Mlsus_error.t (** [false] *)
  | Conj of t * t (** [C1 /\ C2] *)
  | Eq of Type.t * Type.t (** [tau1 = tau2] *)
  | Lower of Type.Var.t (** [lower(a)] *)
  | Exists of Type.Var.t * t (** [exists 'a. C] *)
  | Forall of Type.Var.t list * t (** [forall overline('a). C] *)
  | Let of Var.t * scheme * t (** [let x = sigma in C] *)
  | Instance of Var.t * Type.t (** [x <= tau] *)
  | Instance_scheme of Type.defunctionalized_scheme * Type.t (** [sigma <= tau] *)
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
val forall : Type.Var.t list -> t -> t
val exists_many : Type.Var.t list -> t -> t
val lower : Type.Var.t -> t
val ( #= ) : Var.t -> scheme -> Var.t * scheme

type unquantified_scheme := t * Type.t
type quantified_scheme := (flexibility * Type.Var.t) list * unquantified_scheme

val ( @=> ) : t -> Type.t -> unquantified_scheme
val ( @. ) : (flexibility * Type.Var.t) list -> unquantified_scheme -> quantified_scheme
val mono_scheme : Type.t -> scheme
val poly_scheme : quantified_scheme -> scheme
val let_ : Var.t * scheme -> in_:t -> t
val inst : Var.t -> Type.t -> t
val inst_scm : Type.defunctionalized_scheme -> Type.t -> t

val match_
  :  Type.Var.t
  -> closure:Type.Var.t list
  -> with_:(Type.Matchee.t -> t)
  -> else_:(unit -> t)
  -> t

val with_range : t -> range:Range.t -> t
