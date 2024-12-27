open Core

let open_with_lexbuf ~f filename () =
  let in_ = In_channel.create filename in
  protect
    ~f:(fun () ->
      let lexbuf = Lexing.from_channel in_ in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      f lexbuf)
    ~finally:(fun () -> In_channel.close in_)
;;

let lex_and_print lexbuf =
  let open Mlsus_parser in
  let tokens = Lexer.read_tokens lexbuf in
  match tokens with
  | Ok tokens -> Fmt.(pr "@[<v>%a@]@." (list Token.pp)) tokens
  | Error (`Lexer_error message) -> Fmt.pr "Lexer error: %s.@." message
;;

let parse_and_print lexbuf =
  let open Mlsus_ast in
  let open Mlsus_parser in
  match Parser.parse_structure lexbuf with
  | Ok structure -> Fmt.pr "@[%a@]@." Sexp.pp_hum (Ast.sexp_of_structure structure)
  | Error (`Lexer_error message) -> Fmt.pr "Lexer error: %s.@." message
  | Error `Parser_error -> Fmt.pr "Parser error.@."
;;

let constraint_gen_and_print lexbuf ~dump_ast =
  let open Mlsus_ast in
  let open Mlsus_parser in
  let open Mlsus_type_checker in
  let open Mlsus_constraint in
  match Parser.parse_structure lexbuf with
  | Ok structure ->
    if dump_ast
    then
      Fmt.pr "Parsed structure:@.@[%a@]@.@." Sexp.pp_hum (Ast.sexp_of_structure structure);
    (match infer_str structure with
     | Ok c -> Fmt.pr "@[%a@]@." Sexp.pp_hum (Constraint.sexp_of_t c)
     | Error err -> Fmt.pr "@[%a@]@." Error.pp err)
  | Error (`Lexer_error message) -> Fmt.pr "Lexer error: %s.@." message
  | Error `Parser_error -> Fmt.pr "Parser error.@."
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
        +> flag "--dump-ast" no_arg ~doc:"Dumps the parsed program (formatted as a sexp).")
      (fun filename dump_ast ->
        open_with_lexbuf ~f:(constraint_gen_and_print ~dump_ast) filename)
  ;;

  let command =
    Command.group
      ~summary:"mlsus"
      [ "lex", lex; "parse", parse; "constraint-gen", constraint_gen ]
  ;;
end

let () = Command_unix.run Command.command
