open Core
open Grace

module Token = struct
  include Token

  type t = token

  let pp ppf t =
    match t with
    | WITH -> Fmt.pf ppf "With"
    | UPPER_IDENT uident -> Fmt.pf ppf "Upper_ident(%s)" uident
    | UNDERSCORE -> Fmt.pf ppf "Underscore"
    | TYPE -> Fmt.pf ppf "Type"
    | THEN -> Fmt.pf ppf "Then"
    | STAR -> Fmt.pf ppf "Star"
    | SLASH -> Fmt.pf ppf "Slash"
    | SEMI_SEMI_COLON -> Fmt.pf ppf "Semi_semi_colon"
    | SEMI_COLON -> Fmt.pf ppf "Semi_colon"
    | RIGHT_PAREN -> Fmt.pf ppf "Right_paren"
    | RIGHT_BRACE -> Fmt.pf ppf "Right_brace"
    | RIGHT_ARROW -> Fmt.pf ppf "Right_arrow"
    | QUOTE -> Fmt.pf ppf "Quote"
    | PLUS -> Fmt.pf ppf "Plus"
    | OVER -> Fmt.pf ppf "Over"
    | OF -> Fmt.pf ppf "Of"
    | MINUS -> Fmt.pf ppf "Minus"
    | MATCH -> Fmt.pf ppf "Match"
    | LET -> Fmt.pf ppf "Let"
    | LESS_GREATER -> Fmt.pf ppf "Less_greater"
    | LESS_EQUAL -> Fmt.pf ppf "Less_equal"
    | LESS -> Fmt.pf ppf "Less"
    | LEFT_PAREN -> Fmt.pf ppf "Left_paren"
    | LEFT_BRACE -> Fmt.pf ppf "Left_brace"
    | IN -> Fmt.pf ppf "In"
    | IF -> Fmt.pf ppf "If"
    | IDENT ident -> Fmt.pf ppf "Ident(%s)" ident
    | GREATER_EQUAL -> Fmt.pf ppf "Greater_equal"
    | GREATER -> Fmt.pf ppf "Greater"
    | FUN -> Fmt.pf ppf "Fun"
    | EXTERNAL -> Fmt.pf ppf "External"
    | EXISTS -> Fmt.pf ppf "Exists"
    | FORALL -> Fmt.pf ppf "Forall"
    | EQUAL -> Fmt.pf ppf "Equal"
    | EOF -> Fmt.pf ppf "Eof"
    | ELSE -> Fmt.pf ppf "Else"
    | DOT -> Fmt.pf ppf "Dot"
    | CONST_UNIT -> Fmt.pf ppf "Const_unit"
    | CONST_TRUE -> Fmt.pf ppf "Const_true"
    | CONST_INT i -> Fmt.pf ppf "Const_int(%d)" i
    | CONST_FALSE -> Fmt.pf ppf "Const_false"
    | COMMA -> Fmt.pf ppf "Comma"
    | COLON -> Fmt.pf ppf "Colon"
    | BAR_BAR -> Fmt.pf ppf "Bar_bar"
    | BAR -> Fmt.pf ppf "Bar"
    | AS -> Fmt.pf ppf "As"
    | AND_AND -> Fmt.pf ppf "And_and"
    | AND -> Fmt.pf ppf "And"
  ;;

  let is_eof t =
    match t with
    | EOF -> true
    | _ -> false
  ;;

  let to_string = Fmt.to_to_string pp
end

module Lexer = struct
  let raw_read_token = Lexer.read

  let read_token ?source lexbuf =
    Mlsus_source.with_optional_source ?source @@ fun () -> raw_read_token lexbuf
  ;;

  let read_tokens ?source ?(keep_eof = false) lexbuf =
    Mlsus_source.with_optional_source ?source
    @@ fun () ->
    let rec loop acc =
      let tok = raw_read_token lexbuf in
      if Token.is_eof tok then if keep_eof then tok :: acc else acc else loop (tok :: acc)
    in
    loop [] |> List.rev
  ;;
end

module Parser = struct
  type 'a t = ?source:Source.t -> Lexing.lexbuf -> 'a

  let parse ~f ?source lexbuf =
    Mlsus_source.with_optional_source ?source
    @@ fun () ->
    try f Lexer.raw_read_token lexbuf with
    | Parser.Error ->
      Mlsus_error.(raise @@ syntax_error ~range:(Range.of_lexbuf ?source lexbuf))
  ;;

  let parse_core_type = parse ~f:Parser.parse_core_type
  let parse_expression = parse ~f:Parser.parse_expression
  let parse_structure = parse ~f:Parser.parse_structure
end
