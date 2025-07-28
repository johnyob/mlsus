open Core
open Incr

module T = struct
  open Base_quickcheck

  type t = (int[@quickcheck.generator Generator.int_inclusive 0 999])
  [@@deriving equal, compare, sexp, hash, bin_io, quickcheck]
end

include T
include Comparable.Make (T)

type source = { next_id : unit -> t }

let create_source () =
  let next_id = ref 0 in
  { next_id = (fun () -> post_incr next_id) }
;;

let create source = source.next_id ()
