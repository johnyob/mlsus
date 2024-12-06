open Base

(** This module implements an imperative data structure for disjoint sets
    (commonly known as `union-find'), based on Tarjan and Huet.

    Union find implements a family of disjoint sets on values, where
    the disjoint sets can dynamically be combined using [union].

    This implementation is optimized for the representation of equivalent
    classes. Each equivalence class containing a "value".

    This implementation is not (yet) thread-safe. *)

(** The type ['a t] denotes a node in an equivalence class associated with a
    unique value of type ['a]. *)
type 'a t [@@deriving sexp_of]

include Invariant.S1 with type 'a t := 'a t

(** [create v] creates a new node representing a singleton class with value [v]. *)
val create : 'a -> 'a t

(** [get t] returns the value of the equivalence class of [t]. *)
val get : 'a t -> 'a

(** [set t v] sets the value of the equivalence class of [t] to [v]. *)
val set : 'a t -> 'a -> unit

(** [union t1 t2 ~f] merges the equivalence classes of [t1] and [t2].
    The value of the combined class is given by [f (get t1) (get t2)].

    After [union t1 t2 ~f], [t1 === t2] always holds true. *)
val union : 'a t -> 'a t -> f:('a -> 'a -> 'a) -> unit

(** [same_class t1 t2] returns true iff [t1] and [t2] belong to the same
    equivalence class. *)
val same_class : 'a t -> 'a t -> bool

(** [is_root t] returns true if [t] is the root of an equivalence class *)
val is_root : 'a t -> bool