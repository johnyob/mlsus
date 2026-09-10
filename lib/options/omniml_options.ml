open Core

module Option = struct
  module T = struct
    type t =
      | First_class_polymorphism
      | Defaulting
      | Recursive_types
      | Include_stdlib
      | Dump_ast
      | Dump_constraint
    [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

type t =
  { first_class_polymorphism : bool
  ; defaulting : bool
  ; recursive_types : bool
  ; include_stdlib : bool
  ; dump_ast : bool
  ; dump_constraint : bool
  }

let empty =
  { first_class_polymorphism = false
  ; defaulting = false
  ; recursive_types = false
  ; include_stdlib = false
  ; dump_ast = false
  ; dump_constraint = false
  }
;;

let is_enabled t option =
  match option with
  | Option.First_class_polymorphism -> t.first_class_polymorphism
  | Defaulting -> t.defaulting
  | Recursive_types -> t.recursive_types
  | Include_stdlib -> t.include_stdlib
  | Dump_ast -> t.dump_ast
  | Dump_constraint -> t.dump_constraint
;;

let with_ t ~option ~enabled =
  match option with
  | Option.First_class_polymorphism -> { t with first_class_polymorphism = enabled }
  | Defaulting -> { t with defaulting = enabled }
  | Recursive_types -> { t with recursive_types = enabled }
  | Include_stdlib -> { t with include_stdlib = enabled }
  | Dump_ast -> { t with dump_ast = enabled }
  | Dump_constraint -> { t with dump_constraint = enabled }
;;
