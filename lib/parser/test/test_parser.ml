open! Import

let parse_and_print ~parser sexp_of input =
  let lexbuf = Lexing.from_string input in
  match parser lexbuf with
  | Ok x -> Fmt.(pr "@[<v>%a@]@." Sexp.pp_hum) (sexp_of x)
  | Error err -> Fmt.pr "@[%a@]@." Parser.Error.pp err
;;

let parse_and_print_structure =
  parse_and_print ~parser:Parser.parse_structure [%sexp_of: Ast.structure]
;;

let parse_and_print_expression =
  parse_and_print ~parser:Parser.parse_expression [%sexp_of: Ast.expression]
;;

let parse_and_print_core_type =
  parse_and_print ~parser:Parser.parse_core_type [%sexp_of: Ast.core_type]
;;

let%expect_test "variable : alphas" =
  let exp =
    {|
      hello_world_var
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_var hello_world_var) |}]
;;

let%expect_test "variable : alphanum" =
  let exp =
    {|
      hello_world_var_123
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_var hello_world_var_123) |}]
;;

let%expect_test "variable : prime" =
  let exp =
    {|
      x'
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_var x') |}]
;;

let%expect_test "constructor : alpha" =
  let exp =
    {|
      Nil
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_constr Nil ()) |}]
;;

let%expect_test "constructor : all" =
  let exp =
    {|
      True_false_11'
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_constr True_false_11' ()) |}]
;;

let%expect_test "constant : unit" =
  let exp = {| () |} in
  parse_and_print_expression exp;
  [%expect {| (Exp_const Const_unit) |}]
;;

let%expect_test "constant : int" =
  let exp = {| 5000 |} in
  parse_and_print_expression exp;
  [%expect {| (Exp_const (Const_int 5000)) |}]
;;

let%expect_test "constant : int (prefixed)" =
  let exp =
    {|
      -10
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_const (Const_int -10)) |}]
;;

let%expect_test "constant : bool" =
  let exp = {| false |} in
  parse_and_print_expression exp;
  [%expect {| (Exp_const (Const_bool false)) |}]
;;

let%expect_test "primitive : binary operators" =
  let exp = {| (5 + 4 - 8 * 2) / 2 = 0 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_app
     (Exp_app (Exp_var "( = )")
      (Exp_app
       (Exp_app (Exp_var "( / )")
        (Exp_app
         (Exp_app (Exp_var "( - )")
          (Exp_app (Exp_app (Exp_var "( + )") (Exp_const (Const_int 5)))
           (Exp_const (Const_int 4))))
         (Exp_app (Exp_app (Exp_var "( * )") (Exp_const (Const_int 8)))
          (Exp_const (Const_int 2)))))
       (Exp_const (Const_int 2))))
     (Exp_const (Const_int 0)))
    |}]
;;

let%expect_test "core_type : type var" =
  let type_ = {| 'a |} in
  parse_and_print_core_type type_;
  [%expect {| (Type_var a) |}]
;;

let%expect_test "core_type : function" =
  let type_ = {| (int -> int) -> int -> int |} in
  parse_and_print_core_type type_;
  [%expect
    {|
    (Type_arrow (Type_arrow (Type_constr () int) (Type_constr () int))
     (Type_arrow (Type_constr () int) (Type_constr () int)))
    |}]
;;

let%expect_test "core_type : tuple" =
  let type_ = {| int * int * int |} in
  parse_and_print_core_type type_;
  [%expect
    {| (Type_tuple ((Type_constr () int) (Type_constr () int) (Type_constr () int))) |}]
;;

let%expect_test "core_type : constr" =
  let type_ = {| (int * 'a) list |} in
  parse_and_print_core_type type_;
  [%expect {| (Type_constr ((Type_tuple ((Type_constr () int) (Type_var a)))) list) |}]
;;

let%expect_test "if" =
  let exp =
    {|
      if true then 3 else 4
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_if_then_else (Exp_const (Const_bool true)) (Exp_const (Const_int 3))
     (Exp_const (Const_int 4)))
    |}]
;;

let%expect_test "fun : identity" =
  let exp = {| fun x -> x |} in
  parse_and_print_expression exp;
  [%expect {| (Exp_fun (Pat_var x) (Exp_var x)) |}]
;;

let%expect_test "fun : fst" =
  let exp = {| fun (x, y) -> x |} in
  parse_and_print_expression exp;
  [%expect {| (Exp_fun (Pat_tuple ((Pat_var x) (Pat_var y))) (Exp_var x)) |}]
;;

let%expect_test "fun : map" =
  let exp =
    {|  let map = fix (fun map t f -> 
          match t with 
            ( Nil -> Nil
            | Cons -> Cons (f x, map t f) ) )
        in ()
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_let
     ((value_binding_var map)
      (value_binding_exp
       (Exp_app (Exp_var fix)
        (Exp_fun (Pat_var map)
         (Exp_fun (Pat_var t)
          (Exp_fun (Pat_var f)
           (Exp_match (Exp_var t)
            (((case_lhs (Pat_constr Nil ())) (case_rhs (Exp_constr Nil ())))
             ((case_lhs (Pat_constr Cons ()))
              (case_rhs
               (Exp_constr Cons
                ((Exp_tuple
                  ((Exp_app (Exp_var f) (Exp_var x))
                   (Exp_app (Exp_app (Exp_var map) (Exp_var t)) (Exp_var f))))))))))))))))
     (Exp_const Const_unit))
    |}]
;;

let%expect_test "annotation : exists" =
  let exp =
    {| exists (type 'a 'b) -> 
        fun (x : 'a) -> (x : 'b)
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_exists (a b)
     (Exp_fun (Pat_annot (Pat_var x) (Type_var a))
      (Exp_annot (Exp_var x) (Type_var b))))
    |}]
;;

let%expect_test "let : fact" =
  let exp =
    {| let fact = fix (fun fact n -> 
        if n = 0 then 1 else n * fact (n - 1) )
       in ()
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_let
     ((value_binding_var fact)
      (value_binding_exp
       (Exp_app (Exp_var fix)
        (Exp_fun (Pat_var fact)
         (Exp_fun (Pat_var n)
          (Exp_if_then_else
           (Exp_app (Exp_app (Exp_var "( = )") (Exp_var n))
            (Exp_const (Const_int 0)))
           (Exp_const (Const_int 1))
           (Exp_app (Exp_app (Exp_var "( * )") (Exp_var n))
            (Exp_app (Exp_var fact)
             (Exp_app (Exp_app (Exp_var "( - )") (Exp_var n))
              (Exp_const (Const_int 1)))))))))))
     (Exp_const Const_unit))
    |}]
;;

let%expect_test "tuples" =
  let exp = {| (1, 2, 3, (5, 6, 7), (), ((1,2,3))) |} in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_tuple
     ((Exp_const (Const_int 1)) (Exp_const (Const_int 2))
      (Exp_const (Const_int 3))
      (Exp_tuple
       ((Exp_const (Const_int 5)) (Exp_const (Const_int 6))
        (Exp_const (Const_int 7))))
      (Exp_const Const_unit)
      (Exp_tuple
       ((Exp_const (Const_int 1)) (Exp_const (Const_int 2))
        (Exp_const (Const_int 3))))))
    |}]
;;

let%expect_test "function - uncurry" =
  let exp = {| fun f (x, y) -> f x y |} in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_fun (Pat_var f)
     (Exp_fun (Pat_tuple ((Pat_var x) (Pat_var y)))
      (Exp_app (Exp_app (Exp_var f) (Exp_var x)) (Exp_var y))))
    |}]
;;

let%expect_test "pattern : constant" =
  let exp =
    {|
      fun 1 -> ()
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_fun (Pat_const (Const_int 1)) (Exp_const Const_unit)) |}]
;;

let%expect_test "pattern : wildcard" =
  let exp =
    {|
      fun _ -> ()
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_fun Pat_any (Exp_const Const_unit)) |}]
;;

let%expect_test "pattern : constructor" =
  let exp =
    {|
      fun (Cons (x, t)) -> x
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_fun (Pat_constr Cons ((Pat_tuple ((Pat_var x) (Pat_var t)))))
     (Exp_var x))
    |}]
;;

let%expect_test "pattern : tuple" =
  let exp =
    {|
      fun (x, _, _, _) -> x
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_fun (Pat_tuple ((Pat_var x) Pat_any Pat_any Pat_any)) (Exp_var x)) |}]
;;

let%expect_test "pattern : annotation" =
  let exp =
    {|
      fun (x : 'a) -> x
    |}
  in
  parse_and_print_expression exp;
  [%expect {| (Exp_fun (Pat_annot (Pat_var x) (Type_var a)) (Exp_var x)) |}]
;;

let%expect_test "pattern : as" =
  let exp =
    {|
      fun ((Cons (x as y, _)) as t) -> y
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    (Exp_fun
     (Pat_alias
      (Pat_constr Cons ((Pat_tuple ((Pat_alias (Pat_var x) y) Pat_any)))) t)
     (Exp_var y))
    |}]
;;

let%expect_test "variable : doesn't begin w/ lower alpha" =
  let exp = {| _x |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "core_type : unclosed tuple" =
  let exp = {| (x : int * ) |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "core_type : trailing argument comma" =
  let exp = {| (x : ('a, ) list) |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "core_type : trailing arrow" =
  let exp = {| (x : int -> ) |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "let : no function syntax" =
  let exp = {| let fst (x, y) = x in () |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "let : trailing in" =
  let exp = {| let x = 1 |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "if : trailing else" =
  let exp = {| if true then 3 |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "pattern : swap expr and pat" =
  let exp = {| fun (fun () -> a) -> _ |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "pattern : non-atomic pattern" =
  let exp = {| fun Cons x as t -> 1 |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "unclosed brackets" =
  let exp = {| ((1 + 1) + 2 |} in
  parse_and_print_expression exp;
  [%expect {| Parser error |}]
;;

let%expect_test "unterminated comment" =
  let exp =
    {|
      (* This function does some cool stuff
      let foo () = bar in ()
    |}
  in
  parse_and_print_expression exp;
  [%expect {| Lexer error: "Unclosed comment" |}]
;;

let%expect_test "top level function definition" =
  let str =
    {| 
      let smallest_integer = 0;;
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    ((Str_value
      ((value_binding_var smallest_integer)
       (value_binding_exp (Exp_const (Const_int 0))))))
    |}]
;;

let%expect_test "type definitions - ADTs" =
  let str =
    {|
      type 'a list = 
        | Nil (* empty list - "nil" *)
        | Cons of 'a * 'a list (* list constructor - "cons" *)
      ;;
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    ((Str_type
      (((type_decl_name list) (type_decl_params (a))
        (type_decl_kind
         (Type_decl_variant
          (((constructor_name Nil) (constructor_arg ()))
           ((constructor_name Cons)
            (constructor_arg
             ((Type_tuple ((Type_var a) (Type_constr ((Type_var a)) list)))))))))))))
    |}]
;;

let%expect_test "type definition - abstract" =
  let str =
    {|
      type zero;;
      type 'n succ;;
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    ((Str_type
      (((type_decl_name zero) (type_decl_params ())
        (type_decl_kind Type_decl_abstract))))
     (Str_type
      (((type_decl_name succ) (type_decl_params (n))
        (type_decl_kind Type_decl_abstract)))))
    |}]
;;

let%expect_test "eval example" =
  let str =
    {|
      type bin_op = Add | Sub;;

      type expr = 
        | Int of int
        | Var of string
        | Let of (string * expr) list * expr
        | Bin_op of expr * bin_op * expr
      ;;

      let eval_bin_op = fun op n1 n2 -> 
        match op with
        ( Add -> n1 + n2
        | Sub -> n1 - n2
        )
      ;;


      let eval = fix (fun eval env exp ->
        match exp with
        ( Int n -> n
        | Var x -> env_find env x
        | Let (bindings, in_) -> 
          let env = 
            list_fold_right bindings env (fun (var, exp) env ->
              env_bind env var exp)
          in 
          eval env in_
        | Bin_op (left, op, right) ->
          let n1 = eval env left in
          let n2 = eval env right in
          eval_bin_op op n1 n2
        )
      );;
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    ((Str_type
      (((type_decl_name bin_op) (type_decl_params ())
        (type_decl_kind
         (Type_decl_variant
          (((constructor_name Add) (constructor_arg ()))
           ((constructor_name Sub) (constructor_arg ()))))))))
     (Str_type
      (((type_decl_name expr) (type_decl_params ())
        (type_decl_kind
         (Type_decl_variant
          (((constructor_name Int) (constructor_arg ((Type_constr () int))))
           ((constructor_name Var) (constructor_arg ((Type_constr () string))))
           ((constructor_name Let)
            (constructor_arg
             ((Type_tuple
               ((Type_constr
                 ((Type_tuple ((Type_constr () string) (Type_constr () expr))))
                 list)
                (Type_constr () expr))))))
           ((constructor_name Bin_op)
            (constructor_arg
             ((Type_tuple
               ((Type_constr () expr) (Type_constr () bin_op)
                (Type_constr () expr))))))))))))
     (Str_value
      ((value_binding_var eval_bin_op)
       (value_binding_exp
        (Exp_fun (Pat_var op)
         (Exp_fun (Pat_var n1)
          (Exp_fun (Pat_var n2)
           (Exp_match (Exp_var op)
            (((case_lhs (Pat_constr Add ()))
              (case_rhs
               (Exp_app (Exp_app (Exp_var "( + )") (Exp_var n1)) (Exp_var n2))))
             ((case_lhs (Pat_constr Sub ()))
              (case_rhs
               (Exp_app (Exp_app (Exp_var "( - )") (Exp_var n1)) (Exp_var n2))))))))))))
     (Str_value
      ((value_binding_var eval)
       (value_binding_exp
        (Exp_app (Exp_var fix)
         (Exp_fun (Pat_var eval)
          (Exp_fun (Pat_var env)
           (Exp_fun (Pat_var exp)
            (Exp_match (Exp_var exp)
             (((case_lhs (Pat_constr Int ((Pat_var n)))) (case_rhs (Exp_var n)))
              ((case_lhs (Pat_constr Var ((Pat_var x))))
               (case_rhs
                (Exp_app (Exp_app (Exp_var env_find) (Exp_var env)) (Exp_var x))))
              ((case_lhs
                (Pat_constr Let ((Pat_tuple ((Pat_var bindings) (Pat_var in_))))))
               (case_rhs
                (Exp_let
                 ((value_binding_var env)
                  (value_binding_exp
                   (Exp_app
                    (Exp_app
                     (Exp_app (Exp_var list_fold_right) (Exp_var bindings))
                     (Exp_var env))
                    (Exp_fun (Pat_tuple ((Pat_var var) (Pat_var exp)))
                     (Exp_fun (Pat_var env)
                      (Exp_app
                       (Exp_app (Exp_app (Exp_var env_bind) (Exp_var env))
                        (Exp_var var))
                       (Exp_var exp)))))))
                 (Exp_app (Exp_app (Exp_var eval) (Exp_var env)) (Exp_var in_)))))
              ((case_lhs
                (Pat_constr Bin_op
                 ((Pat_tuple ((Pat_var left) (Pat_var op) (Pat_var right))))))
               (case_rhs
                (Exp_let
                 ((value_binding_var n1)
                  (value_binding_exp
                   (Exp_app (Exp_app (Exp_var eval) (Exp_var env))
                    (Exp_var left))))
                 (Exp_let
                  ((value_binding_var n2)
                   (value_binding_exp
                    (Exp_app (Exp_app (Exp_var eval) (Exp_var env))
                     (Exp_var right))))
                  (Exp_app
                   (Exp_app (Exp_app (Exp_var eval_bin_op) (Exp_var op))
                    (Exp_var n1))
                   (Exp_var n2))))))))))))))))
    |}]
;;

let%expect_test "top level external definitions" =
  let str =
    {|
      external greater_than : int -> int -> bool;;

      external to_sexp : 'a. 'a -> sexp;;
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    ((Str_primitive
      ((value_name greater_than)
       (value_type
        ((scheme_quantifiers ())
         (scheme_body
          (Type_arrow (Type_constr () int)
           (Type_arrow (Type_constr () int) (Type_constr () bool))))))))
     (Str_primitive
      ((value_name to_sexp)
       (value_type
        ((scheme_quantifiers (a))
         (scheme_body (Type_arrow (Type_var a) (Type_constr () sexp))))))))
    |}]
;;

let%expect_test "no trailing ;;" =
  let str =
    {|
      let valid_function = fun () -> 1
    |}
  in
  parse_and_print_structure str;
  [%expect {| Parser error |}]
;;

let%expect_test "type definition - empty case" =
  let str =
    {|
      type t = 
        |
        | A of int
        | B of bool 
      ;;
    |}
  in
  parse_and_print_structure str;
  [%expect {| Parser error |}]
;;

let%expect_test "type definition - empty variant" =
  let str =
    {|
      type t = |;;
    |}
  in
  parse_and_print_structure str;
  [%expect {| Parser error |}]
;;
