open Core
open Grace

(* This module defines auxiliary AST types used by [Ast] types. *)

type constant =
  | Const_int of int
  | Const_bool of bool
  | Const_unit
[@@deriving sexp_of]

module With_range = struct
  type 'a t =
    { it : 'a
    ; range : Range.t
    }
  [@@deriving sexp_of]

  let create ~range it = { it; range }
  let it t = t.it
end

module Ident = struct
  module type S = sig
    type t = private string

    val create : string -> t

    include Identifiable.S with type t := t

    module With_range : sig
      type nonrec t = t With_range.t [@@deriving sexp_of]
    end
  end

  module Make () : S = struct
    include String

    let create s = s

    module With_range = struct
      type nonrec t = t With_range.t [@@deriving sexp_of]
    end
  end
end

module Var_name = Ident.Make ()
module Type_var_name = Ident.Make ()
module Type_name = Ident.Make ()
module Constructor_name = Ident.Make ()
module Label_name = Ident.Make ()
