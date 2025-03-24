open Core
open Mlsus_ast
open Mlsus_parser
open Mlsus_constraint

let pp_structure ppf structure =
  Fmt.pf ppf "@[%a@]" Sexp.pp_hum ([%sexp_of: Ast.structure] structure)
;;

let lex_and_print ?source lexbuf =
  Mlsus_error.handle_uncaught ~exit:true
  @@ fun () ->
  let tokens = Lexer.read_tokens ?source lexbuf in
  Fmt.(pr "@[<v>%a@]@." (list Token.pp)) tokens
;;

let parse ?source lexbuf = Parser.parse_structure ?source lexbuf
let parse_and_print ?source lexbuf = Fmt.pr "%a@." pp_structure (parse ?source lexbuf)

let constraint_gen ?source lexbuf ~dump_ast =
  let structure = parse ?source lexbuf in
  if dump_ast then Fmt.pr "Parsed structure:@.%a.@." pp_structure structure;
  Mlsus_type_checker.infer_str structure
;;

let pp_constraint ppf cst = Fmt.pf ppf "@[%a@]" Sexp.pp_hum ([%sexp_of: Constraint.t] cst)

let constraint_gen_and_print ?source lexbuf ~dump_ast =
  Mlsus_error.handle_uncaught ~exit:true
  @@ fun () ->
  let cst = constraint_gen ?source lexbuf ~dump_ast in
  Fmt.pr "%a@." pp_constraint cst
;;

let type_check_and_print ?source lexbuf ~dump_ast ~dump_constraint =
  Mlsus_error.handle_uncaught ~exit:true
  @@ fun () ->
  let cst = constraint_gen ?source lexbuf ~dump_ast in
  if dump_constraint then Fmt.pr "Generated constraint:@.%a@." pp_constraint cst;
  match Mlsus_constraint_solver.solve cst with
  | Ok () -> Fmt.pr "Well typed :)@."
  | Error err ->
    Fmt.pr
      "@[%a@]@."
      Sexp.pp_hum
      [%message "Failed to solve constraint" (err : Mlsus_constraint_solver.Error.t)]
;;
