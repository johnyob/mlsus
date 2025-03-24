open Core
open Async
open Mlsus_main

let open_with_lexbuf ~f filename () =
  let in_ = In_channel.create filename in
  protect
    ~f:(fun () ->
      let lexbuf = Lexing.from_channel in_ in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      f lexbuf)
    ~finally:(fun () -> In_channel.close in_)
;;

module Command = struct
  let lex =
    Command.basic_spec
      ~summary:"Lexes [filename] and prints the tokens."
      Command.Spec.(empty +> anon ("filename" %: string))
      (open_with_lexbuf ~f:lex_and_print)
  ;;

  let parse =
    Command.basic_spec
      ~summary:"Parses [filename] and prints the program (formatted as a sexp)."
      Command.Spec.(empty +> anon ("filename" %: string))
      (open_with_lexbuf ~f:parse_and_print)
  ;;

  let constraint_gen =
    Command.basic_spec
      ~summary:
        "Parses [filename] and prints the generated constraint (formatted as a sexp)."
      Command.Spec.(
        empty
        +> anon ("filename" %: string)
        +> flag "-dump-ast" no_arg ~doc:"Dumps the parsed program (formatted as a sexp).")
      (fun filename dump_ast ->
         open_with_lexbuf ~f:(constraint_gen_and_print ~dump_ast) filename)
  ;;

  let type_check =
    Async_command.async_spec
      ~summary:"Type checks [filename]."
      Command.Spec.(
        empty
        +> anon ("filename" %: string)
        +> flag "-dump-ast" no_arg ~doc:"Dumps the parsed program (formatted as a sexp)."
        +> flag
             "-dump-constraint"
             no_arg
             ~doc:"Dumps the generated constraint (formatted as a sexp)."
        +> Async_log.Global.set_level_via_param ())
      (fun filename dump_ast dump_constraint () ->
         open_with_lexbuf filename ~f:(fun lexbuf ->
           let () = type_check_and_print ~dump_ast ~dump_constraint lexbuf in
           Async_log.Global.flushed ()))
  ;;

  let v =
    Command.group
      ~summary:"mlsus"
      [ "lex", lex
      ; "parse", parse
      ; "constraint-gen", constraint_gen
      ; "type-check", type_check
      ]
  ;;
end

let () = Command_unix.run Command.v
