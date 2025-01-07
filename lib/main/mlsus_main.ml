open Core
open Mlsus_ast
open Mlsus_parser
open Mlsus_constraint

let pp_structure ppf structure =
  Fmt.pf ppf "@[%a@]" Sexp.pp_hum ([%sexp_of: Ast.structure] structure)
;;

let lex_and_print lexbuf =
  match Lexer.read_tokens lexbuf with
  | Ok tokens -> Fmt.(pr "@[<v>%a@]@." (list Token.pp)) tokens
  | Error err -> Fmt.pr "@[%a@]@." Lexer.Error.pp err
;;

let parse ?source lexbuf k =
  match Parser.parse_structure ?source lexbuf with
  | Ok structure -> k structure
  | Error err -> Fmt.pr "@[%a@]@." Parser.Error.pp err
;;

let parse_and_print ?source lexbuf =
  parse ?source lexbuf @@ fun structure -> Fmt.pr "%a@." pp_structure structure
;;

let constraint_gen ?source lexbuf ~dump_ast k =
  parse ?source lexbuf
  @@ fun structure ->
  if dump_ast then Fmt.pr "Parsed structure:@.%a.@." pp_structure structure;
  match Mlsus_type_checker.infer_str structure with
  | Ok cst -> k cst
  | Error err -> Fmt.pr "@[%a@]@." Error.pp err
;;

let pp_constraint ppf cst = Fmt.pf ppf "@[%a@]" Sexp.pp_hum ([%sexp_of: Constraint.t] cst)

let constraint_gen_and_print ?source lexbuf ~dump_ast =
  constraint_gen ?source lexbuf ~dump_ast @@ fun cst -> Fmt.pr "%a@." pp_constraint cst
;;

let type_check_and_print ?source lexbuf ~dump_ast ~dump_constraint =
  constraint_gen ?source lexbuf ~dump_ast
  @@ fun cst ->
  if dump_constraint then Fmt.pr "Generated constraint:@.%a@." pp_constraint cst;
  match Mlsus_constraint_solver.solve cst with
  | Ok () -> Fmt.pr "Well typed :)@."
  | Error err -> Fmt.pr "@[%a@]@." Error.pp err
;;
