open Core
open Omniml_ast
open Omniml_parser
module Constraint = Omniml_constraint_solver.Constraint
module Options = Omniml_options
module Typed_ast = Omniml_typed_ast.Typed_ast

let pp_structure ppf structure =
  Fmt.pf ppf "@[%a@]" Sexp.pp_hum ([%sexp_of: Ast.structure] structure)
;;

let lex_and_print ?source lexbuf =
  let tokens = Lexer.read_tokens ?source lexbuf in
  Fmt.(pr "@[<v>%a@]@." (list Token.pp)) tokens
;;

let parse ?source lexbuf = Parser.parse_structure ?source lexbuf
let parse_and_print ?source lexbuf = Fmt.pr "%a@." pp_structure (parse ?source lexbuf)

let constraint_gen ?source lexbuf ~dump_ast ~with_stdlib =
  let structure = parse ?source lexbuf in
  if dump_ast then Fmt.pr "Parsed structure:@.%a.@." pp_structure structure;
  Omniml_type_checker.infer_str ~with_stdlib structure
;;

let pp_constraint ppf cst = Fmt.pf ppf "@[%a@]" Sexp.pp_hum ([%sexp_of: Constraint.t] cst)

let constraint_gen_and_print ?source lexbuf ~dump_ast ~with_stdlib ~with_fcp =
  let cst = constraint_gen ?source lexbuf ~dump_ast ~with_stdlib ~with_fcp in
  Fmt.pr "%a@." pp_constraint cst
;;

let type_check_and_print
      ?source
      lexbuf
      ~dump_ast
      ~dump_constraint
      ~with_stdlib
      ~with_fcp
      ~defaulting
  =
  let cst = constraint_gen ?source lexbuf ~dump_ast ~with_stdlib ~with_fcp in
  if dump_constraint then Fmt.pr "Generated constraint:@.%a@." pp_constraint cst;
  let range =
    let open Grace in
    Option.(
      source
      >>| fun source ->
      Range.create ~source Byte_index.initial (Byte_index.of_int @@ Source.length source))
  in
  let signature = Omniml_type_checker.check ~defaulting ?range cst in
  Fmt.pr "%a@." Typed_ast.pp signature
;;
