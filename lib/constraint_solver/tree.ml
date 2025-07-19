open! Import

module Level : sig
  type t = private int [@@deriving equal, compare, sexp, hash]

  include Comparable.S with type t := t

  val zero : t
  val succ : t -> t
end = struct
  module T = struct
    type t = int [@@deriving equal, compare, sexp, hash]
  end

  include T
  include Comparable.Make (T)

  let zero = 0
  let succ t = t + 1
end

type 'a node =
  { id : Identifier.t
  ; level : Level.t
  ; value : 'a
  ; parent : 'a node option
  }
[@@deriving sexp_of]

and 'a t = T of 'a node [@@unboxed] [@@deriving sexp_of]

let root (T root) = root

let create ~id_source value =
  T { id = Identifier.create id_source; parent = None; level = Level.zero; value }
;;

let create_node ~id_source ~parent value =
  let level = Level.succ parent.level in
  { id = Identifier.create id_source; parent = Some parent; level; value }
;;

let rec nearest_common_ancestor t1 t2 =
  [%log.global.debug
    "nearest common ancestor" (t1.id : Identifier.t) (t2.id : Identifier.t)];
  if Identifier.(t1.id = t2.id)
  then t1
  else if Level.(t1.level < t2.level)
  then nearest_common_ancestor t1 (Option.value_exn ~here:[%here] t2.parent)
  else if Level.(t1.level > t2.level)
  then nearest_common_ancestor (Option.value_exn ~here:[%here] t1.parent) t2
  else (
    assert (Level.(t1.level = t2.level && t1.level > zero));
    nearest_common_ancestor
      (Option.value_exn ~here:[%here] t1.parent)
      (Option.value_exn ~here:[%here] t2.parent))
;;

let compare_node_by_level n1 n2 = Level.compare n1.level n2.level [@@inline]
