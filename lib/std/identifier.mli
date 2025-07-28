open Core

(** A unique identifier represented as a 63-bit integer *)
type t = private int [@@deriving equal, compare, sexp, hash, bin_io, quickcheck]

include Comparable.S with type t := t

(** A source of identifiers. See [Identifier.create]. *)
type source

(** [create_source ()] returns a fresh identifier source. *)
val create_source : unit -> source

(** [create source] returns a fresh identifier (wrt to the [source]). *)
val create : source -> t
