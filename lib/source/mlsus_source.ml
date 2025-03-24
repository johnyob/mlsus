open Core
open Grace

let state : Source.t option ref = ref None
let get () = !state

let get_exn () =
  match !state with
  | Some src -> src
  | None ->
    Mlsus_error.(raise @@ bug_s ~here:[%here] [%message "State is not initialized"])
;;

let assert_state_is_empty () =
  if Option.is_some !state
  then
    Mlsus_error.(
      raise
      @@ bug_s
           ~here:[%here]
           [%message "State is already initialized" (!state : Source.t option)])
;;

let init_optional src =
  assert_state_is_empty ();
  state := src
;;

let init src =
  assert_state_is_empty ();
  state := Some src
;;

let clear () = state := None

let with_source ~source f =
  Fun.protect
    (fun () ->
       init source;
       f ())
    ~finally:clear
;;

let with_optional_source ?source f =
  Fun.protect
    (fun () ->
       init_optional source;
       f ())
    ~finally:clear
;;

module For_testing = struct
  let expect_test_source str : Source.t =
    (* Grace's `string_source` has a frustrating bug in `sexp_of_string_source`
       which prints the contents of string source out. This results in a huge expect
       test output. A quick fix is to construct a string source manually (using a reader source) *)
    `Reader
      { id = 0
      ; name = Some "expect_test.ml"
      ; length = String.length str
      ; unsafe_get = String.unsafe_get str
      }
  ;;
end
