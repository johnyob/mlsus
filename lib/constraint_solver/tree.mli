open! Import

module Level : sig
  (** The depth of a node in a tree *)
  type t = private int [@@deriving equal, compare, sexp, hash]

  include Comparable.S with type t := t
end

(** A tree consists of a value and a number of children.
    The level of a node within the tree represents the node's depth. *)
type 'a node =
  { id : Identifier.t (** Unique identifier of the node *)
  ; level : Level.t
    (** The level of the node in the tree.
      If [parent] is [None], then [level = Level.zero],
      otherwise [level = Level.succ parent.level]. *)
  ; value : 'a (** The region of the node *)
  ; parent : 'a node option (** Parent of the node, if [None] then node is a root node. *)
  }
[@@deriving sexp_of]

and 'a t = T of 'a node [@@unboxed] [@@deriving sexp_of]

(** [root t] returns the root node of the tree *)
val root : 'a t -> 'a node

(** [create ~id_source ~region] returns a new tree *)
val create : id_source:Identifier.source -> 'a -> 'a t

(** [create_node ~id_source ~parent ~region] returns a new region node with parent [parent] *)
val create_node : id_source:Identifier.source -> parent:'a node -> 'a -> 'a node

(** [nearest_common_ancestor n1 n2] returns the nearest common ancestor of two nodes in a tree *)
val nearest_common_ancestor : 'a node -> 'a node -> 'a node

(** [compare_node_by_level n1 n2] is [Level.compare n1.level n2.level]. *)
val compare_node_by_level : 'a node -> 'a node -> int
