open Core

module Option : sig
  type t =
    | First_class_polymorphism
    | Defaulting
    | Recursive_types
    | Include_stdlib
    | Dump_ast
    | Dump_constraint
  [@@deriving sexp]

  include Comparable.S with type t := t
end

type t

val empty : t
val is_enabled : t -> Option.t -> bool
val with_ : t -> option:Option.t -> enabled:bool -> t
