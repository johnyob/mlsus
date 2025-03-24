open! Import

let () = Mlsus_error.For_testing.use_expect_test_config ()

let lex_and_print input =
  Mlsus_error.handle_uncaught ~exit:false
  @@ fun () ->
  let source = Mlsus_source.For_testing.expect_test_source input in
  let lexbuf = Lexing.from_string input in
  let tokens = Lexer.read_tokens ~source lexbuf in
  Fmt.(pr "@[<v>%a@]@." (list Token.pp)) tokens
;;

let%expect_test "unterminated comment" =
  let str = {| (* This is a very interesting comment |} in
  lex_and_print str;
  [%expect
    {|
    error[E001]: unterminated comment
        ┌─ expect_test.ml:1:40
      1 │   (* This is a very interesting comment
        │                                         ^
    |}]
;;

let%expect_test "single-line comment" =
  let str = {| (* Some comment here *) |} in
  lex_and_print str;
  [%expect {| |}]
;;

let%expect_test "multi-line comment" =
  let str =
    {| 
      (* This is a very long 
         and interesting comment 
      *) 
    |}
  in
  lex_and_print str;
  [%expect {| |}]
;;

let%expect_test "keywords" =
  [ "let"
  ; "and"
  ; "in"
  ; "if"
  ; "then"
  ; "else"
  ; "fun"
  ; "match"
  ; "with"
  ; "exists"
  ; "type"
  ; "as"
  ; "of"
  ; "external"
  ; ";;"
  ; "->"
  ; ":"
  ; "="
  ; "."
  ; ","
  ; ";"
  ; "*"
  ; "_"
  ; "'"
  ; "|"
  ; "+"
  ; "-"
  ; "/"
  ; "true"
  ; "false"
  ; "()"
  ; "("
  ; ")"
  ; "<"
  ; ">"
  ; ">="
  ; "<="
  ; "<>"
  ]
  |> List.iter ~f:(fun keyword ->
    Fmt.pr "Keyword: %s @.Output: " keyword;
    lex_and_print keyword);
  [%expect
    {|
    Keyword: let
    Output: Let
    Keyword: and
    Output: And
    Keyword: in
    Output: In
    Keyword: if
    Output: If
    Keyword: then
    Output: Then
    Keyword: else
    Output: Else
    Keyword: fun
    Output: Fun
    Keyword: match
    Output: Match
    Keyword: with
    Output: With
    Keyword: exists
    Output: Exists
    Keyword: type
    Output: Type
    Keyword: as
    Output: As
    Keyword: of
    Output: Of
    Keyword: external
    Output: External
    Keyword: ;;
    Output: Semi_semi_colon
    Keyword: ->
    Output: Right_arrow
    Keyword: :
    Output: Colon
    Keyword: =
    Output: Equal
    Keyword: .
    Output: Dot
    Keyword: ,
    Output: Comma
    Keyword: ;
    Output: Semi_colon
    Keyword: *
    Output: Star
    Keyword: _
    Output: Underscore
    Keyword: '
    Output: Quote
    Keyword: |
    Output: Bar
    Keyword: +
    Output: Plus
    Keyword: -
    Output: Minus
    Keyword: /
    Output: Slash
    Keyword: true
    Output: Const_true
    Keyword: false
    Output: Const_false
    Keyword: ()
    Output: Const_unit
    Keyword: (
    Output: Left_paren
    Keyword: )
    Output: Right_paren
    Keyword: <
    Output: Less
    Keyword: >
    Output: Greater
    Keyword: >=
    Output: Greater_equal
    Keyword: <=
    Output: Less_equal
    Keyword: <>
    Output: Less_greater
    |}]
;;

let%expect_test "ints" =
  [ "1"; "0"; "0123456789"; "-42" ]
  |> List.iter ~f:(fun int_ ->
    Fmt.pr "Int: %s @.Output: " int_;
    lex_and_print int_);
  [%expect
    {|
    Int: 1
    Output: Const_int(1)
    Int: 0
    Output: Const_int(0)
    Int: 0123456789
    Output: Const_int(123456789)
    Int: -42
    Output: Const_int(-42)
    |}]
;;

let%expect_test "ident" =
  [ "x"
  ; "type_"
  ; "lident"
  ; "x1"
  ; "snake_case"
  ; "prime'"
  ; "prime_numbers10998927898723178923''''"
  ]
  |> List.iter ~f:(fun ident ->
    Fmt.pr "Ident: %s @.Output: " ident;
    lex_and_print ident);
  [%expect
    {|
    Ident: x
    Output: Ident(x)
    Ident: type_
    Output: Ident(type_)
    Ident: lident
    Output: Ident(lident)
    Ident: x1
    Output: Ident(x1)
    Ident: snake_case
    Output: Ident(snake_case)
    Ident: prime'
    Output: Ident(prime')
    Ident: prime_numbers10998927898723178923''''
    Output: Ident(prime_numbers10998927898723178923'''')
    |}]
;;

let%expect_test "upper_ident" =
  [ "X"
  ; "Cons"
  ; "Nil"
  ; "Cannot_unify"
  ; "Left_brace"
  ; "Prime'"
  ; "Primes''''"
  ; "Numbers1029347583"
  ; "Everything_1234_foo_bar''''''"
  ]
  |> List.iter ~f:(fun uident ->
    Fmt.pr "Upper_ident: %s @.Output: " uident;
    lex_and_print uident);
  [%expect
    {|
    Upper_ident: X
    Output: Upper_ident(X)
    Upper_ident: Cons
    Output: Upper_ident(Cons)
    Upper_ident: Nil
    Output: Upper_ident(Nil)
    Upper_ident: Cannot_unify
    Output: Upper_ident(Cannot_unify)
    Upper_ident: Left_brace
    Output: Upper_ident(Left_brace)
    Upper_ident: Prime'
    Output: Upper_ident(Prime')
    Upper_ident: Primes''''
    Output: Upper_ident(Primes'''')
    Upper_ident: Numbers1029347583
    Output: Upper_ident(Numbers1029347583)
    Upper_ident: Everything_1234_foo_bar''''''
    Output: Upper_ident(Everything_1234_foo_bar'''''')
    |}]
;;
