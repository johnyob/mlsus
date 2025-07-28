open Core

module type S = sig
  type t = private
    { id : Identifier.t
    ; name : string
    }
  [@@deriving quickcheck]

  val create : id_source:Identifier.source -> ?name:string -> unit -> t

  include Identifiable.S with type t := t
end

module Make (X : sig
    val module_name : string
  end) : S = struct
  module T = struct
    type t =
      { id : Identifier.t
      ; name : string
      }
    [@@deriving equal, compare, hash, bin_io, sexp, quickcheck]

    let create ~id_source ?(name = X.module_name) () =
      { id = Identifier.create id_source; name }
    ;;

    let of_string s = s |> Sexp.of_string |> t_of_sexp
    let to_string t = t |> sexp_of_t |> Sexp.to_string

    include X
  end

  include T
  include Identifiable.Make (T)
end
