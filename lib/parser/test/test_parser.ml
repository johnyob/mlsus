open! Import

let () = Mlsus_error.For_testing.use_expect_test_config ()

let parse_and_print ~parser sexp_of input =
  Mlsus_error.handle_uncaught ~exit:false
  @@ fun () ->
  let source = Mlsus_source.For_testing.expect_test_source input in
  let lexbuf = Lexing.from_string ~with_positions:true input in
  let x = parser ?source:(Some source) lexbuf in
  Fmt.(pr "@[<v>%a@]@." Sexp.pp_hum) (sexp_of x)
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
  [%expect
    {|
    ((it
      (Exp_var
       ((it hello_world_var)
        (range
         ((start 7) (stop 22)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 27) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 22)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 27) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "variable : alphanum" =
  let exp =
    {|
      hello_world_var_123
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_var
       ((it hello_world_var_123)
        (range
         ((start 7) (stop 26)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 31) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 26)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 31) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "variable : prime" =
  let exp =
    {|
      x'
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_var
       ((it x')
        (range
         ((start 7) (stop 9)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 14) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 9)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 14) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "constructor : alpha" =
  let exp =
    {|
      Nil
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_constr
       ((it Nil)
        (range
         ((start 7) (stop 10)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 15) (unsafe_get <fun>)))))))
       ()))
     (range
      ((start 7) (stop 10)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 15) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "constructor : all" =
  let exp =
    {|
      True_false_11'
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_constr
       ((it True_false_11')
        (range
         ((start 7) (stop 21)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 26) (unsafe_get <fun>)))))))
       ()))
     (range
      ((start 7) (stop 21)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 26) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "constant : unit" =
  let exp = {| () |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it (Exp_const Const_unit))
     (range
      ((start 1) (stop 3)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 4) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "constant : int" =
  let exp = {| 5000 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it (Exp_const (Const_int 5000)))
     (range
      ((start 1) (stop 5)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 6) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "constant : int (prefixed)" =
  let exp =
    {|
      -10
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it (Exp_const (Const_int -10)))
     (range
      ((start 7) (stop 10)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 15) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "constant : bool" =
  let exp = {| false |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it (Exp_const (Const_bool false)))
     (range
      ((start 1) (stop 6)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 7) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "primitive : binary operators" =
  let exp = {| (5 + 4 - 8 * 2) / 2 = 0 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_app
       ((it
         (Exp_app
          ((it
            (Exp_var
             ((it "( = )")
              (range
               ((start 21) (stop 22)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))))
           (range
            ((start 1) (stop 24)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))
          ((it
            (Exp_app
             ((it
               (Exp_app
                ((it
                  (Exp_var
                   ((it "( / )")
                    (range
                     ((start 17) (stop 18)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 25)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 1) (stop 20)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 25)
                      (unsafe_get <fun>)))))))
                ((it
                  (Exp_app
                   ((it
                     (Exp_app
                      ((it
                        (Exp_var
                         ((it "( - )")
                          (range
                           ((start 8) (stop 9)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 25)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 2) (stop 15)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 25)
                            (unsafe_get <fun>)))))))
                      ((it
                        (Exp_app
                         ((it
                           (Exp_app
                            ((it
                              (Exp_var
                               ((it "( + )")
                                (range
                                 ((start 4) (stop 5)
                                  (source
                                   (Reader
                                    ((id 0) (name (expect_test.ml)) (length 25)
                                     (unsafe_get <fun>)))))))))
                             (range
                              ((start 2) (stop 7)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 25)
                                  (unsafe_get <fun>)))))))
                            ((it (Exp_const (Const_int 5)))
                             (range
                              ((start 2) (stop 3)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 25)
                                  (unsafe_get <fun>)))))))))
                          (range
                           ((start 2) (stop 7)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 25)
                               (unsafe_get <fun>)))))))
                         ((it (Exp_const (Const_int 4)))
                          (range
                           ((start 6) (stop 7)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 25)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 2) (stop 7)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 25)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 2) (stop 15)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 25)
                         (unsafe_get <fun>)))))))
                   ((it
                     (Exp_app
                      ((it
                        (Exp_app
                         ((it
                           (Exp_var
                            ((it "( * )")
                             (range
                              ((start 12) (stop 13)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 25)
                                  (unsafe_get <fun>)))))))))
                          (range
                           ((start 10) (stop 15)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 25)
                               (unsafe_get <fun>)))))))
                         ((it (Exp_const (Const_int 8)))
                          (range
                           ((start 10) (stop 11)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 25)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 10) (stop 15)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 25)
                            (unsafe_get <fun>)))))))
                      ((it (Exp_const (Const_int 2)))
                       (range
                        ((start 14) (stop 15)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 25)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 10) (stop 15)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 25)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 2) (stop 15)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 25)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 1) (stop 20)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))
             ((it (Exp_const (Const_int 2)))
              (range
               ((start 19) (stop 20)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))))
           (range
            ((start 1) (stop 20)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))))
        (range
         ((start 1) (stop 24)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))
       ((it (Exp_const (Const_int 0)))
        (range
         ((start 23) (stop 24)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 24)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 25) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "core_type : type var" =
  let type_ = {| 'a |} in
  parse_and_print_core_type type_;
  [%expect
    {|
    ((it
      (Type_var
       ((it a)
        (range
         ((start 1) (stop 3)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 4) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 3)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 4) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "core_type : function" =
  let type_ = {| (int -> int) -> int -> int |} in
  parse_and_print_core_type type_;
  [%expect
    {|
    ((it
      (Type_arrow
       ((it
         (Type_arrow
          ((it
            (Type_constr ()
             ((it int)
              (range
               ((start 2) (stop 5)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
           (range
            ((start 2) (stop 5)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))
          ((it
            (Type_constr ()
             ((it int)
              (range
               ((start 9) (stop 12)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
           (range
            ((start 8) (stop 12)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
        (range
         ((start 2) (stop 12)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))
       ((it
         (Type_arrow
          ((it
            (Type_constr ()
             ((it int)
              (range
               ((start 17) (stop 20)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
           (range
            ((start 16) (stop 20)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))
          ((it
            (Type_constr ()
             ((it int)
              (range
               ((start 24) (stop 27)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
           (range
            ((start 23) (stop 27)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
        (range
         ((start 17) (stop 27)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 27)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 28) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "core_type : tuple" =
  let type_ = {| int * int * int |} in
  parse_and_print_core_type type_;
  [%expect
    {|
    ((it
      (Type_tuple
       (((it
          (Type_constr ()
           ((it int)
            (range
             ((start 1) (stop 4)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))))
         (range
          ((start 0) (stop 4)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
        ((it
          (Type_constr ()
           ((it int)
            (range
             ((start 7) (stop 10)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))))
         (range
          ((start 6) (stop 10)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
        ((it
          (Type_constr ()
           ((it int)
            (range
             ((start 13) (stop 16)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))))
         (range
          ((start 12) (stop 16)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>))))))))))
     (range
      ((start 1) (stop 16)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "core_type : constr" =
  let type_ = {| (int * 'a) list |} in
  parse_and_print_core_type type_;
  [%expect
    {|
    ((it
      (Type_constr
       (((it
          (Type_tuple
           (((it
              (Type_constr ()
               ((it int)
                (range
                 ((start 2) (stop 5)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 17)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 2) (stop 5)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
            ((it
              (Type_var
               ((it a)
                (range
                 ((start 8) (stop 10)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 17)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 8) (stop 10)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>))))))))))
         (range
          ((start 2) (stop 10)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>))))))))
       ((it list)
        (range
         ((start 12) (stop 16)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 16)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
    |}]
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
    ((it
      (Exp_if_then_else
       ((it (Exp_const (Const_bool true)))
        (range
         ((start 10) (stop 14)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
       ((it (Exp_const (Const_int 3)))
        (range
         ((start 20) (stop 21)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
       ((it (Exp_const (Const_int 4)))
        (range
         ((start 27) (stop 28)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 28)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "fun : identity" =
  let exp = {| fun x -> x |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it
          (Pat_var
           ((it x)
            (range
             ((start 5) (stop 6)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 12) (unsafe_get <fun>)))))))))
         (range
          ((start 5) (stop 6)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 12) (unsafe_get <fun>))))))))
       ((it
         (Exp_var
          ((it x)
           (range
            ((start 10) (stop 11)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 12) (unsafe_get <fun>)))))))))
        (range
         ((start 10) (stop 11)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 12) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 11)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 12) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "fun : fst" =
  let exp = {| fun (x, y) -> x |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it
          (Pat_tuple
           (((it
              (Pat_var
               ((it x)
                (range
                 ((start 6) (stop 7)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 17)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 6) (stop 7)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
            ((it
              (Pat_var
               ((it y)
                (range
                 ((start 9) (stop 10)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 17)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 9) (stop 10)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>))))))))))
         (range
          ((start 5) (stop 11)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>))))))))
       ((it
         (Exp_var
          ((it x)
           (range
            ((start 15) (stop 16)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))))
        (range
         ((start 15) (stop 16)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 16)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 17) (unsafe_get <fun>)))))))
    |}]
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
    ((it
      (Exp_let
       ((it
         ((value_binding_var
           ((it map)
            (range
             ((start 6) (stop 9)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 146) (unsafe_get <fun>))))))))
          (value_binding_over_flag Non_overloaded)
          (value_binding_exp
           ((it
             (Exp_app
              ((it
                (Exp_var
                 ((it fix)
                  (range
                   ((start 12) (stop 15)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 146)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 12) (stop 15)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 146)
                    (unsafe_get <fun>)))))))
              ((it
                (Exp_fun
                 (((it
                    (Pat_var
                     ((it map)
                      (range
                       ((start 21) (stop 24)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 146)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 21) (stop 24)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 146)
                        (unsafe_get <fun>)))))))
                  ((it
                    (Pat_var
                     ((it t)
                      (range
                       ((start 25) (stop 26)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 146)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 25) (stop 26)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 146)
                        (unsafe_get <fun>)))))))
                  ((it
                    (Pat_var
                     ((it f)
                      (range
                       ((start 27) (stop 28)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 146)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 27) (stop 28)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 146)
                        (unsafe_get <fun>))))))))
                 ((it
                   (Exp_match
                    ((it
                      (Exp_var
                       ((it t)
                        (range
                         ((start 49) (stop 50)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 146)
                             (unsafe_get <fun>)))))))))
                     (range
                      ((start 49) (stop 50)
                       (source
                        (Reader
                         ((id 0) (name (expect_test.ml)) (length 146)
                          (unsafe_get <fun>)))))))
                    (((it
                       ((case_lhs
                         ((it
                           (Pat_constr
                            ((it Nil)
                             (range
                              ((start 71) (stop 74)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 146)
                                  (unsafe_get <fun>)))))))
                            ()))
                          (range
                           ((start 71) (stop 74)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 146)
                               (unsafe_get <fun>))))))))
                        (case_rhs
                         ((it
                           (Exp_constr
                            ((it Nil)
                             (range
                              ((start 78) (stop 81)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 146)
                                  (unsafe_get <fun>)))))))
                            ()))
                          (range
                           ((start 78) (stop 81)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 146)
                               (unsafe_get <fun>))))))))))
                      (range
                       ((start 71) (stop 81)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 146)
                           (unsafe_get <fun>)))))))
                     ((it
                       ((case_lhs
                         ((it
                           (Pat_constr
                            ((it Cons)
                             (range
                              ((start 96) (stop 100)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 146)
                                  (unsafe_get <fun>)))))))
                            ()))
                          (range
                           ((start 96) (stop 100)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 146)
                               (unsafe_get <fun>))))))))
                        (case_rhs
                         ((it
                           (Exp_constr
                            ((it Cons)
                             (range
                              ((start 104) (stop 108)
                               (source
                                (Reader
                                 ((id 0) (name (expect_test.ml)) (length 146)
                                  (unsafe_get <fun>)))))))
                            (((it
                               (Exp_tuple
                                (((it
                                   (Exp_app
                                    ((it
                                      (Exp_var
                                       ((it f)
                                        (range
                                         ((start 110) (stop 111)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 146) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 110) (stop 111)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 146) (unsafe_get <fun>)))))))
                                    ((it
                                      (Exp_var
                                       ((it x)
                                        (range
                                         ((start 112) (stop 113)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 146) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 112) (stop 113)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 146) (unsafe_get <fun>)))))))))
                                  (range
                                   ((start 110) (stop 113)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 146) (unsafe_get <fun>)))))))
                                 ((it
                                   (Exp_app
                                    ((it
                                      (Exp_app
                                       ((it
                                         (Exp_var
                                          ((it map)
                                           (range
                                            ((start 115) (stop 118)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 146) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 115) (stop 118)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 146) (unsafe_get <fun>)))))))
                                       ((it
                                         (Exp_var
                                          ((it t)
                                           (range
                                            ((start 119) (stop 120)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 146) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 119) (stop 120)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 146) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 115) (stop 120)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 146) (unsafe_get <fun>)))))))
                                    ((it
                                      (Exp_var
                                       ((it f)
                                        (range
                                         ((start 121) (stop 122)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 146) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 121) (stop 122)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 146) (unsafe_get <fun>)))))))))
                                  (range
                                   ((start 115) (stop 122)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 146) (unsafe_get <fun>))))))))))
                              (range
                               ((start 109) (stop 123)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 146)
                                   (unsafe_get <fun>))))))))))
                          (range
                           ((start 104) (stop 123)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 146)
                               (unsafe_get <fun>))))))))))
                      (range
                       ((start 96) (stop 123)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 146)
                           (unsafe_get <fun>))))))))))
                  (range
                   ((start 43) (stop 125)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 146)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 17) (stop 125)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 146)
                    (unsafe_get <fun>)))))))))
            (range
             ((start 12) (stop 127)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 146) (unsafe_get <fun>))))))))))
        (range
         ((start 5) (stop 127)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 146) (unsafe_get <fun>)))))))
       ((it (Exp_const Const_unit))
        (range
         ((start 139) (stop 141)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 146) (unsafe_get <fun>)))))))))
     (range
      ((start 2) (stop 141)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 146) (unsafe_get <fun>)))))))
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
    ((it
      (Exp_exists
       (((it a)
         (range
          ((start 14) (stop 16)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>)))))))
        ((it b)
         (range
          ((start 17) (stop 19)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>))))))))
       ((it
         (Exp_fun
          (((it
             (Pat_annot
              ((it
                (Pat_var
                 ((it x)
                  (range
                   ((start 38) (stop 39)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 62)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 38) (stop 39)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 62)
                    (unsafe_get <fun>)))))))
              ((it
                (Type_var
                 ((it a)
                  (range
                   ((start 42) (stop 44)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 62)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 42) (stop 44)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 62)
                    (unsafe_get <fun>)))))))))
            (range
             ((start 37) (stop 45)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>))))))))
          ((it
            (Exp_annot
             ((it
               (Exp_var
                ((it x)
                 (range
                  ((start 50) (stop 51)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 62)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 50) (stop 51)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>)))))))
             ((it
               (Type_var
                ((it b)
                 (range
                  ((start 54) (stop 56)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 62)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 54) (stop 56)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>)))))))))
           (range
            ((start 49) (stop 57)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>)))))))))
        (range
         ((start 33) (stop 57)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 57)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 62) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "annotation : forall" =
  let exp =
    {| forall (type 'a) -> 
        fun (x : 'a) -> (x : 'a)
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_forall
       (((it a)
         (range
          ((start 14) (stop 16)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>))))))))
       ((it
         (Exp_fun
          (((it
             (Pat_annot
              ((it
                (Pat_var
                 ((it x)
                  (range
                   ((start 35) (stop 36)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 59)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 35) (stop 36)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 59)
                    (unsafe_get <fun>)))))))
              ((it
                (Type_var
                 ((it a)
                  (range
                   ((start 39) (stop 41)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 59)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 39) (stop 41)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 59)
                    (unsafe_get <fun>)))))))))
            (range
             ((start 34) (stop 42)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>))))))))
          ((it
            (Exp_annot
             ((it
               (Exp_var
                ((it x)
                 (range
                  ((start 47) (stop 48)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 59)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 47) (stop 48)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>)))))))
             ((it
               (Type_var
                ((it a)
                 (range
                  ((start 51) (stop 53)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 59)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 51) (stop 53)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>)))))))))
           (range
            ((start 46) (stop 54)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>)))))))))
        (range
         ((start 30) (stop 54)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 54)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 59) (unsafe_get <fun>)))))))
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
    ((it
      (Exp_let
       ((it
         ((value_binding_var
           ((it fact)
            (range
             ((start 5) (stop 9)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 97) (unsafe_get <fun>))))))))
          (value_binding_over_flag Non_overloaded)
          (value_binding_exp
           ((it
             (Exp_app
              ((it
                (Exp_var
                 ((it fix)
                  (range
                   ((start 12) (stop 15)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 97)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 12) (stop 15)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 97)
                    (unsafe_get <fun>)))))))
              ((it
                (Exp_fun
                 (((it
                    (Pat_var
                     ((it fact)
                      (range
                       ((start 21) (stop 25)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 97)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 21) (stop 25)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 97)
                        (unsafe_get <fun>)))))))
                  ((it
                    (Pat_var
                     ((it n)
                      (range
                       ((start 26) (stop 27)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 97)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 26) (stop 27)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 97)
                        (unsafe_get <fun>))))))))
                 ((it
                   (Exp_if_then_else
                    ((it
                      (Exp_app
                       ((it
                         (Exp_app
                          ((it
                            (Exp_var
                             ((it "( = )")
                              (range
                               ((start 45) (stop 46)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 43) (stop 48)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 97)
                                (unsafe_get <fun>)))))))
                          ((it
                            (Exp_var
                             ((it n)
                              (range
                               ((start 43) (stop 44)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 43) (stop 44)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 97)
                                (unsafe_get <fun>)))))))))
                        (range
                         ((start 43) (stop 48)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 97)
                             (unsafe_get <fun>)))))))
                       ((it (Exp_const (Const_int 0)))
                        (range
                         ((start 47) (stop 48)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 97)
                             (unsafe_get <fun>)))))))))
                     (range
                      ((start 43) (stop 48)
                       (source
                        (Reader
                         ((id 0) (name (expect_test.ml)) (length 97)
                          (unsafe_get <fun>)))))))
                    ((it (Exp_const (Const_int 1)))
                     (range
                      ((start 54) (stop 55)
                       (source
                        (Reader
                         ((id 0) (name (expect_test.ml)) (length 97)
                          (unsafe_get <fun>)))))))
                    ((it
                      (Exp_app
                       ((it
                         (Exp_app
                          ((it
                            (Exp_var
                             ((it "( * )")
                              (range
                               ((start 63) (stop 64)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 61) (stop 77)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 97)
                                (unsafe_get <fun>)))))))
                          ((it
                            (Exp_var
                             ((it n)
                              (range
                               ((start 61) (stop 62)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 61) (stop 62)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 97)
                                (unsafe_get <fun>)))))))))
                        (range
                         ((start 61) (stop 77)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 97)
                             (unsafe_get <fun>)))))))
                       ((it
                         (Exp_app
                          ((it
                            (Exp_var
                             ((it fact)
                              (range
                               ((start 65) (stop 69)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 65) (stop 69)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 97)
                                (unsafe_get <fun>)))))))
                          ((it
                            (Exp_app
                             ((it
                               (Exp_app
                                ((it
                                  (Exp_var
                                   ((it "( - )")
                                    (range
                                     ((start 73) (stop 74)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 97) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 71) (stop 76)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 97)
                                      (unsafe_get <fun>)))))))
                                ((it
                                  (Exp_var
                                   ((it n)
                                    (range
                                     ((start 71) (stop 72)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 97) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 71) (stop 72)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 97)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 71) (stop 76)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))
                             ((it (Exp_const (Const_int 1)))
                              (range
                               ((start 75) (stop 76)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 97)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 71) (stop 76)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 97)
                                (unsafe_get <fun>)))))))))
                        (range
                         ((start 65) (stop 77)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 97)
                             (unsafe_get <fun>)))))))))
                     (range
                      ((start 61) (stop 77)
                       (source
                        (Reader
                         ((id 0) (name (expect_test.ml)) (length 97)
                          (unsafe_get <fun>)))))))))
                  (range
                   ((start 40) (stop 77)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 97)
                       (unsafe_get <fun>)))))))))
               (range
                ((start 17) (stop 77)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 97)
                    (unsafe_get <fun>)))))))))
            (range
             ((start 12) (stop 79)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 97) (unsafe_get <fun>))))))))))
        (range
         ((start 4) (stop 79)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 97) (unsafe_get <fun>)))))))
       ((it (Exp_const Const_unit))
        (range
         ((start 90) (stop 92)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 97) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 92)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 97) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "tuples" =
  let exp = {| (1, 2, 3, (5, 6, 7), (), ((1,2,3))) |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_tuple
       (((it (Exp_const (Const_int 1)))
         (range
          ((start 2) (stop 3)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
        ((it (Exp_const (Const_int 2)))
         (range
          ((start 5) (stop 6)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
        ((it (Exp_const (Const_int 3)))
         (range
          ((start 8) (stop 9)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
        ((it
          (Exp_tuple
           (((it (Exp_const (Const_int 5)))
             (range
              ((start 12) (stop 13)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
            ((it (Exp_const (Const_int 6)))
             (range
              ((start 15) (stop 16)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
            ((it (Exp_const (Const_int 7)))
             (range
              ((start 18) (stop 19)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>))))))))))
         (range
          ((start 11) (stop 20)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
        ((it (Exp_const Const_unit))
         (range
          ((start 22) (stop 24)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
        ((it
          (Exp_tuple
           (((it (Exp_const (Const_int 1)))
             (range
              ((start 28) (stop 29)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
            ((it (Exp_const (Const_int 2)))
             (range
              ((start 30) (stop 31)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
            ((it (Exp_const (Const_int 3)))
             (range
              ((start 32) (stop 33)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>))))))))))
         (range
          ((start 27) (stop 34)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>))))))))))
     (range
      ((start 1) (stop 36)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 37) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "function - uncurry" =
  let exp = {| fun f (x, y) -> f x y |} in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it
          (Pat_var
           ((it f)
            (range
             ((start 5) (stop 6)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
         (range
          ((start 5) (stop 6)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
        ((it
          (Pat_tuple
           (((it
              (Pat_var
               ((it x)
                (range
                 ((start 8) (stop 9)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 23)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 8) (stop 9)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
            ((it
              (Pat_var
               ((it y)
                (range
                 ((start 11) (stop 12)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 23)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 11) (stop 12)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>))))))))))
         (range
          ((start 7) (stop 13)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>))))))))
       ((it
         (Exp_app
          ((it
            (Exp_app
             ((it
               (Exp_var
                ((it f)
                 (range
                  ((start 17) (stop 18)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 23)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 17) (stop 18)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
             ((it
               (Exp_var
                ((it x)
                 (range
                  ((start 19) (stop 20)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 23)
                      (unsafe_get <fun>)))))))))
              (range
               ((start 19) (stop 20)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
           (range
            ((start 17) (stop 20)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
          ((it
            (Exp_var
             ((it y)
              (range
               ((start 21) (stop 22)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
           (range
            ((start 21) (stop 22)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
        (range
         ((start 17) (stop 22)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
     (range
      ((start 1) (stop 22)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "pattern : constant" =
  let exp =
    {|
      fun 1 -> ()
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it (Pat_const (Const_int 1)))
         (range
          ((start 11) (stop 12)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>))))))))
       ((it (Exp_const Const_unit))
        (range
         ((start 16) (stop 18)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 18)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "pattern : wildcard" =
  let exp =
    {|
      fun _ -> ()
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it Pat_any)
         (range
          ((start 11) (stop 12)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>))))))))
       ((it (Exp_const Const_unit))
        (range
         ((start 16) (stop 18)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 18)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 23) (unsafe_get <fun>)))))))
    |}]
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
    ((it
      (Exp_fun
       (((it
          (Pat_constr
           ((it Cons)
            (range
             ((start 12) (stop 16)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>)))))))
           (((it
              (Pat_tuple
               (((it
                  (Pat_var
                   ((it x)
                    (range
                     ((start 18) (stop 19)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 34)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 18) (stop 19)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 34)
                      (unsafe_get <fun>)))))))
                ((it
                  (Pat_var
                   ((it t)
                    (range
                     ((start 21) (stop 22)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 34)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 21) (stop 22)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 34)
                      (unsafe_get <fun>))))))))))
             (range
              ((start 17) (stop 23)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>))))))))))
         (range
          ((start 12) (stop 23)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>))))))))
       ((it
         (Exp_var
          ((it x)
           (range
            ((start 28) (stop 29)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>)))))))))
        (range
         ((start 28) (stop 29)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 29)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "pattern : tuple" =
  let exp =
    {|
      fun (x, _, _, _) -> x
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it
          (Pat_tuple
           (((it
              (Pat_var
               ((it x)
                (range
                 ((start 12) (stop 13)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 33)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 12) (stop 13)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
            ((it Pat_any)
             (range
              ((start 15) (stop 16)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
            ((it Pat_any)
             (range
              ((start 18) (stop 19)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
            ((it Pat_any)
             (range
              ((start 21) (stop 22)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>))))))))))
         (range
          ((start 11) (stop 23)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>))))))))
       ((it
         (Exp_var
          ((it x)
           (range
            ((start 27) (stop 28)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))))
        (range
         ((start 27) (stop 28)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 28)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 33) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "pattern : annotation" =
  let exp =
    {|
      fun (x : 'a) -> x
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    ((it
      (Exp_fun
       (((it
          (Pat_annot
           ((it
             (Pat_var
              ((it x)
               (range
                ((start 12) (stop 13)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 29)
                    (unsafe_get <fun>)))))))))
            (range
             ((start 12) (stop 13)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 29) (unsafe_get <fun>)))))))
           ((it
             (Type_var
              ((it a)
               (range
                ((start 16) (stop 18)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 29)
                    (unsafe_get <fun>)))))))))
            (range
             ((start 16) (stop 18)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 29) (unsafe_get <fun>)))))))))
         (range
          ((start 11) (stop 19)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 29) (unsafe_get <fun>))))))))
       ((it
         (Exp_var
          ((it x)
           (range
            ((start 23) (stop 24)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 29) (unsafe_get <fun>)))))))))
        (range
         ((start 23) (stop 24)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 29) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 24)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 29) (unsafe_get <fun>)))))))
    |}]
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
    ((it
      (Exp_fun
       (((it
          (Pat_alias
           ((it
             (Pat_constr
              ((it Cons)
               (range
                ((start 13) (stop 17)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 46)
                    (unsafe_get <fun>)))))))
              (((it
                 (Pat_tuple
                  (((it
                     (Pat_alias
                      ((it
                        (Pat_var
                         ((it x)
                          (range
                           ((start 19) (stop 20)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 46)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 19) (stop 20)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 46)
                            (unsafe_get <fun>)))))))
                      ((it y)
                       (range
                        ((start 24) (stop 25)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 46)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 19) (stop 25)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 46)
                         (unsafe_get <fun>)))))))
                   ((it Pat_any)
                    (range
                     ((start 27) (stop 28)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 46)
                         (unsafe_get <fun>))))))))))
                (range
                 ((start 18) (stop 29)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 46)
                     (unsafe_get <fun>))))))))))
            (range
             ((start 13) (stop 29)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 46) (unsafe_get <fun>)))))))
           ((it t)
            (range
             ((start 34) (stop 35)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 46) (unsafe_get <fun>)))))))))
         (range
          ((start 12) (stop 35)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 46) (unsafe_get <fun>))))))))
       ((it
         (Exp_var
          ((it y)
           (range
            ((start 40) (stop 41)
             (source
              (Reader
               ((id 0) (name (expect_test.ml)) (length 46) (unsafe_get <fun>)))))))))
        (range
         ((start 40) (stop 41)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 46) (unsafe_get <fun>)))))))))
     (range
      ((start 7) (stop 41)
       (source
        (Reader ((id 0) (name (expect_test.ml)) (length 46) (unsafe_get <fun>)))))))
    |}]
;;

let%expect_test "variable : doesn't begin w/ lower alpha" =
  let exp = {| _x |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:2
      1 │   _x
        │   ^
    |}]
;;

let%expect_test "core_type : unclosed tuple" =
  let exp = {| (x : int * ) |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:13
      1 │   (x : int * )
        │              ^
    |}]
;;

let%expect_test "core_type : trailing argument comma" =
  let exp = {| (x : ('a, ) list) |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:12
      1 │   (x : ('a, ) list)
        │             ^
    |}]
;;

let%expect_test "core_type : trailing arrow" =
  let exp = {| (x : int -> ) |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:14
      1 │   (x : int -> )
        │               ^
    |}]
;;

let%expect_test "let : no function syntax" =
  let exp = {| let fst (x, y) = x in () |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:10
      1 │   let fst (x, y) = x in ()
        │           ^
    |}]
;;

let%expect_test "let : trailing in" =
  let exp = {| let x = 1 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:12
      1 │   let x = 1
        │             ^
    |}]
;;

let%expect_test "if : trailing else" =
  let exp = {| if true then 3 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:17
      1 │   if true then 3
        │                  ^
    |}]
;;

let%expect_test "pattern : swap expr and pat" =
  let exp = {| fun (fun () -> a) -> _ |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:7
      1 │   fun (fun () -> a) -> _
        │        ^^^
    |}]
;;

let%expect_test "pattern : non-atomic pattern" =
  let exp = {| fun Cons x as t -> 1 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:13
      1 │   fun Cons x as t -> 1
        │              ^^
    |}]
;;

let%expect_test "unclosed brackets" =
  let exp = {| ((1 + 1) + 2 |} in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:1:15
      1 │   ((1 + 1) + 2
        │                ^
    |}]
;;

let%expect_test "unterminated comment" =
  let exp =
    {|
      (* This function does some cool stuff
      let foo () = bar in ()
    |}
  in
  parse_and_print_expression exp;
  [%expect
    {|
    error[E001]: unterminated comment
        ┌─ expect_test.ml:4:5
      4 │
        │      ^
    |}]
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
    (((it
       (Str_value
        ((it
          ((value_binding_var
            ((it smallest_integer)
             (range
              ((start 12) (stop 28)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 39) (unsafe_get <fun>))))))))
           (value_binding_over_flag Non_overloaded)
           (value_binding_exp
            ((it (Exp_const (Const_int 0)))
             (range
              ((start 31) (stop 32)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 39) (unsafe_get <fun>))))))))))
         (range
          ((start 11) (stop 32)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 39) (unsafe_get <fun>)))))))))
      (range
       ((start 8) (stop 32)
        (source
         (Reader ((id 0) (name (expect_test.ml)) (length 39) (unsafe_get <fun>))))))))
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
    (((it
       (Str_type
        (((it
           ((type_decl_name
             ((it list)
              (range
               ((start 15) (stop 19)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 138)
                   (unsafe_get <fun>))))))))
            (type_decl_params
             (((it a)
               (range
                ((start 12) (stop 14)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 138)
                    (unsafe_get <fun>)))))))))
            (type_decl_kind
             (Type_decl_variant
              (((constructor_name
                 ((it Nil)
                  (range
                   ((start 33) (stop 36)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 138)
                       (unsafe_get <fun>))))))))
                (constructor_arg ()))
               ((constructor_name
                 ((it Cons)
                  (range
                   ((start 72) (stop 76)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 138)
                       (unsafe_get <fun>))))))))
                (constructor_arg
                 (((it
                    (Type_tuple
                     (((it
                        (Type_var
                         ((it a)
                          (range
                           ((start 80) (stop 82)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 138)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 80) (stop 82)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 138)
                            (unsafe_get <fun>)))))))
                      ((it
                        (Type_constr
                         (((it
                            (Type_var
                             ((it a)
                              (range
                               ((start 85) (stop 87)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 138)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 85) (stop 87)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 138)
                                (unsafe_get <fun>))))))))
                         ((it list)
                          (range
                           ((start 88) (stop 92)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 138)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 85) (stop 92)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 138)
                            (unsafe_get <fun>))))))))))
                   (range
                    ((start 80) (stop 92)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 138)
                        (unsafe_get <fun>)))))))))))))))
          (range
           ((start 12) (stop 92)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 138) (unsafe_get <fun>))))))))))
      (range
       ((start 7) (stop 92)
        (source
         (Reader
          ((id 0) (name (expect_test.ml)) (length 138) (unsafe_get <fun>))))))))
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
    (((it
       (Str_type
        (((it
           ((type_decl_name
             ((it zero)
              (range
               ((start 12) (stop 16)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 44) (unsafe_get <fun>))))))))
            (type_decl_params ()) (type_decl_kind Type_decl_abstract)))
          (range
           ((start 11) (stop 16)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 44) (unsafe_get <fun>))))))))))
      (range
       ((start 7) (stop 16)
        (source
         (Reader ((id 0) (name (expect_test.ml)) (length 44) (unsafe_get <fun>)))))))
     ((it
       (Str_type
        (((it
           ((type_decl_name
             ((it succ)
              (range
               ((start 33) (stop 37)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 44) (unsafe_get <fun>))))))))
            (type_decl_params
             (((it n)
               (range
                ((start 30) (stop 32)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 44)
                    (unsafe_get <fun>)))))))))
            (type_decl_kind Type_decl_abstract)))
          (range
           ((start 30) (stop 37)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 44) (unsafe_get <fun>))))))))))
      (range
       ((start 25) (stop 37)
        (source
         (Reader ((id 0) (name (expect_test.ml)) (length 44) (unsafe_get <fun>))))))))
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
    (((it
       (Str_type
        (((it
           ((type_decl_name
             ((it bin_op)
              (range
               ((start 12) (stop 18)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 806)
                   (unsafe_get <fun>))))))))
            (type_decl_params ())
            (type_decl_kind
             (Type_decl_variant
              (((constructor_name
                 ((it Add)
                  (range
                   ((start 21) (stop 24)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 806)
                       (unsafe_get <fun>))))))))
                (constructor_arg ()))
               ((constructor_name
                 ((it Sub)
                  (range
                   ((start 27) (stop 30)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 806)
                       (unsafe_get <fun>))))))))
                (constructor_arg ())))))))
          (range
           ((start 11) (stop 30)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))))
      (range
       ((start 7) (stop 30)
        (source
         (Reader
          ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>)))))))
     ((it
       (Str_type
        (((it
           ((type_decl_name
             ((it expr)
              (range
               ((start 45) (stop 49)
                (source
                 (Reader
                  ((id 0) (name (expect_test.ml)) (length 806)
                   (unsafe_get <fun>))))))))
            (type_decl_params ())
            (type_decl_kind
             (Type_decl_variant
              (((constructor_name
                 ((it Int)
                  (range
                   ((start 63) (stop 66)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 806)
                       (unsafe_get <fun>))))))))
                (constructor_arg
                 (((it
                    (Type_constr ()
                     ((it int)
                      (range
                       ((start 70) (stop 73)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 806)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 69) (stop 73)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>))))))))))
               ((constructor_name
                 ((it Var)
                  (range
                   ((start 84) (stop 87)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 806)
                       (unsafe_get <fun>))))))))
                (constructor_arg
                 (((it
                    (Type_constr ()
                     ((it string)
                      (range
                       ((start 91) (stop 97)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 806)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 90) (stop 97)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>))))))))))
               ((constructor_name
                 ((it Let)
                  (range
                   ((start 108) (stop 111)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 806)
                       (unsafe_get <fun>))))))))
                (constructor_arg
                 (((it
                    (Type_tuple
                     (((it
                        (Type_constr
                         (((it
                            (Type_tuple
                             (((it
                                (Type_constr ()
                                 ((it string)
                                  (range
                                   ((start 116) (stop 122)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>)))))))))
                               (range
                                ((start 116) (stop 122)
                                 (source
                                  (Reader
                                   ((id 0) (name (expect_test.ml)) (length 806)
                                    (unsafe_get <fun>)))))))
                              ((it
                                (Type_constr ()
                                 ((it expr)
                                  (range
                                   ((start 125) (stop 129)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>)))))))))
                               (range
                                ((start 124) (stop 129)
                                 (source
                                  (Reader
                                   ((id 0) (name (expect_test.ml)) (length 806)
                                    (unsafe_get <fun>))))))))))
                           (range
                            ((start 116) (stop 129)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))
                         ((it list)
                          (range
                           ((start 131) (stop 135)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 806)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 115) (stop 135)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))
                      ((it
                        (Type_constr ()
                         ((it expr)
                          (range
                           ((start 138) (stop 142)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 806)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 137) (stop 142)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>))))))))))
                   (range
                    ((start 115) (stop 142)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>))))))))))
               ((constructor_name
                 ((it Bin_op)
                  (range
                   ((start 153) (stop 159)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 806)
                       (unsafe_get <fun>))))))))
                (constructor_arg
                 (((it
                    (Type_tuple
                     (((it
                        (Type_constr ()
                         ((it expr)
                          (range
                           ((start 163) (stop 167)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 806)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 162) (stop 167)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))
                      ((it
                        (Type_constr ()
                         ((it bin_op)
                          (range
                           ((start 170) (stop 176)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 806)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 169) (stop 176)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))
                      ((it
                        (Type_constr ()
                         ((it expr)
                          (range
                           ((start 179) (stop 183)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 806)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 178) (stop 183)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>))))))))))
                   (range
                    ((start 163) (stop 183)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>)))))))))))))))
          (range
           ((start 44) (stop 183)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))))
      (range
       ((start 40) (stop 183)
        (source
         (Reader
          ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>)))))))
     ((it
       (Str_value
        ((it
          ((value_binding_var
            ((it eval_bin_op)
             (range
              ((start 204) (stop 215)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))
           (value_binding_over_flag Non_overloaded)
           (value_binding_exp
            ((it
              (Exp_fun
               (((it
                  (Pat_var
                   ((it op)
                    (range
                     ((start 222) (stop 224)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 222) (stop 224)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 806)
                      (unsafe_get <fun>)))))))
                ((it
                  (Pat_var
                   ((it n1)
                    (range
                     ((start 225) (stop 227)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 225) (stop 227)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 806)
                      (unsafe_get <fun>)))))))
                ((it
                  (Pat_var
                   ((it n2)
                    (range
                     ((start 228) (stop 230)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 228) (stop 230)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 806)
                      (unsafe_get <fun>))))))))
               ((it
                 (Exp_match
                  ((it
                    (Exp_var
                     ((it op)
                      (range
                       ((start 249) (stop 251)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 806)
                           (unsafe_get <fun>)))))))))
                   (range
                    ((start 249) (stop 251)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>)))))))
                  (((it
                     ((case_lhs
                       ((it
                         (Pat_constr
                          ((it Add)
                           (range
                            ((start 267) (stop 270)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>)))))))
                          ()))
                        (range
                         ((start 267) (stop 270)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 806)
                             (unsafe_get <fun>))))))))
                      (case_rhs
                       ((it
                         (Exp_app
                          ((it
                            (Exp_app
                             ((it
                               (Exp_var
                                ((it "( + )")
                                 (range
                                  ((start 277) (stop 278)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 274) (stop 281)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             ((it
                               (Exp_var
                                ((it n1)
                                 (range
                                  ((start 274) (stop 276)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 274) (stop 276)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 274) (stop 281)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>)))))))
                          ((it
                            (Exp_var
                             ((it n2)
                              (range
                               ((start 279) (stop 281)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 279) (stop 281)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>)))))))))
                        (range
                         ((start 274) (stop 281)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 806)
                             (unsafe_get <fun>))))))))))
                    (range
                     ((start 267) (stop 281)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>)))))))
                   ((it
                     ((case_lhs
                       ((it
                         (Pat_constr
                          ((it Sub)
                           (range
                            ((start 292) (stop 295)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>)))))))
                          ()))
                        (range
                         ((start 292) (stop 295)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 806)
                             (unsafe_get <fun>))))))))
                      (case_rhs
                       ((it
                         (Exp_app
                          ((it
                            (Exp_app
                             ((it
                               (Exp_var
                                ((it "( - )")
                                 (range
                                  ((start 302) (stop 303)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 299) (stop 306)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             ((it
                               (Exp_var
                                ((it n1)
                                 (range
                                  ((start 299) (stop 301)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 299) (stop 301)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 299) (stop 306)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>)))))))
                          ((it
                            (Exp_var
                             ((it n2)
                              (range
                               ((start 304) (stop 306)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 304) (stop 306)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>)))))))))
                        (range
                         ((start 299) (stop 306)
                          (source
                           (Reader
                            ((id 0) (name (expect_test.ml)) (length 806)
                             (unsafe_get <fun>))))))))))
                    (range
                     ((start 292) (stop 306)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>))))))))))
                (range
                 ((start 243) (stop 316)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 806)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 218) (stop 316)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))))
         (range
          ((start 203) (stop 316)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>)))))))))
      (range
       ((start 200) (stop 316)
        (source
         (Reader
          ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>)))))))
     ((it
       (Str_value
        ((it
          ((value_binding_var
            ((it eval)
             (range
              ((start 338) (stop 342)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))
           (value_binding_over_flag Non_overloaded)
           (value_binding_exp
            ((it
              (Exp_app
               ((it
                 (Exp_var
                  ((it fix)
                   (range
                    ((start 345) (stop 348)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>)))))))))
                (range
                 ((start 345) (stop 348)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 806)
                     (unsafe_get <fun>)))))))
               ((it
                 (Exp_fun
                  (((it
                     (Pat_var
                      ((it eval)
                       (range
                        ((start 354) (stop 358)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 354) (stop 358)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>)))))))
                   ((it
                     (Pat_var
                      ((it env)
                       (range
                        ((start 359) (stop 362)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 359) (stop 362)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>)))))))
                   ((it
                     (Pat_var
                      ((it exp)
                       (range
                        ((start 363) (stop 366)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 363) (stop 366)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 806)
                         (unsafe_get <fun>))))))))
                  ((it
                    (Exp_match
                     ((it
                       (Exp_var
                        ((it exp)
                         (range
                          ((start 384) (stop 387)
                           (source
                            (Reader
                             ((id 0) (name (expect_test.ml)) (length 806)
                              (unsafe_get <fun>)))))))))
                      (range
                       ((start 384) (stop 387)
                        (source
                         (Reader
                          ((id 0) (name (expect_test.ml)) (length 806)
                           (unsafe_get <fun>)))))))
                     (((it
                        ((case_lhs
                          ((it
                            (Pat_constr
                             ((it Int)
                              (range
                               ((start 403) (stop 406)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             (((it
                                (Pat_var
                                 ((it n)
                                  (range
                                   ((start 407) (stop 408)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>)))))))))
                               (range
                                ((start 407) (stop 408)
                                 (source
                                  (Reader
                                   ((id 0) (name (expect_test.ml)) (length 806)
                                    (unsafe_get <fun>))))))))))
                           (range
                            ((start 403) (stop 408)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))
                         (case_rhs
                          ((it
                            (Exp_var
                             ((it n)
                              (range
                               ((start 412) (stop 413)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 412) (stop 413)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))))
                       (range
                        ((start 403) (stop 413)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))
                      ((it
                        ((case_lhs
                          ((it
                            (Pat_constr
                             ((it Var)
                              (range
                               ((start 424) (stop 427)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             (((it
                                (Pat_var
                                 ((it x)
                                  (range
                                   ((start 428) (stop 429)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>)))))))))
                               (range
                                ((start 428) (stop 429)
                                 (source
                                  (Reader
                                   ((id 0) (name (expect_test.ml)) (length 806)
                                    (unsafe_get <fun>))))))))))
                           (range
                            ((start 424) (stop 429)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))
                         (case_rhs
                          ((it
                            (Exp_app
                             ((it
                               (Exp_app
                                ((it
                                  (Exp_var
                                   ((it env_find)
                                    (range
                                     ((start 433) (stop 441)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 433) (stop 441)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))
                                ((it
                                  (Exp_var
                                   ((it env)
                                    (range
                                     ((start 442) (stop 445)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 442) (stop 445)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 433) (stop 445)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             ((it
                               (Exp_var
                                ((it x)
                                 (range
                                  ((start 446) (stop 447)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 446) (stop 447)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 433) (stop 447)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))))
                       (range
                        ((start 424) (stop 447)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))
                      ((it
                        ((case_lhs
                          ((it
                            (Pat_constr
                             ((it Let)
                              (range
                               ((start 458) (stop 461)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             (((it
                                (Pat_tuple
                                 (((it
                                    (Pat_var
                                     ((it bindings)
                                      (range
                                       ((start 463) (stop 471)
                                        (source
                                         (Reader
                                          ((id 0) (name (expect_test.ml))
                                           (length 806) (unsafe_get <fun>)))))))))
                                   (range
                                    ((start 463) (stop 471)
                                     (source
                                      (Reader
                                       ((id 0) (name (expect_test.ml))
                                        (length 806) (unsafe_get <fun>)))))))
                                  ((it
                                    (Pat_var
                                     ((it in_)
                                      (range
                                       ((start 473) (stop 476)
                                        (source
                                         (Reader
                                          ((id 0) (name (expect_test.ml))
                                           (length 806) (unsafe_get <fun>)))))))))
                                   (range
                                    ((start 473) (stop 476)
                                     (source
                                      (Reader
                                       ((id 0) (name (expect_test.ml))
                                        (length 806) (unsafe_get <fun>))))))))))
                               (range
                                ((start 462) (stop 477)
                                 (source
                                  (Reader
                                   ((id 0) (name (expect_test.ml)) (length 806)
                                    (unsafe_get <fun>))))))))))
                           (range
                            ((start 458) (stop 477)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))
                         (case_rhs
                          ((it
                            (Exp_let
                             ((it
                               ((value_binding_var
                                 ((it env)
                                  (range
                                   ((start 496) (stop 499)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>))))))))
                                (value_binding_over_flag Non_overloaded)
                                (value_binding_exp
                                 ((it
                                   (Exp_app
                                    ((it
                                      (Exp_app
                                       ((it
                                         (Exp_app
                                          ((it
                                            (Exp_var
                                             ((it list_fold_right)
                                              (range
                                               ((start 515) (stop 530)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))))
                                           (range
                                            ((start 515) (stop 530)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))
                                          ((it
                                            (Exp_var
                                             ((it bindings)
                                              (range
                                               ((start 531) (stop 539)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))))
                                           (range
                                            ((start 531) (stop 539)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 515) (stop 539)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))
                                       ((it
                                         (Exp_var
                                          ((it env)
                                           (range
                                            ((start 540) (stop 543)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 540) (stop 543)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 515) (stop 543)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 806) (unsafe_get <fun>)))))))
                                    ((it
                                      (Exp_fun
                                       (((it
                                          (Pat_tuple
                                           (((it
                                              (Pat_var
                                               ((it var)
                                                (range
                                                 ((start 550) (stop 553)
                                                  (source
                                                   (Reader
                                                    ((id 0)
                                                     (name (expect_test.ml))
                                                     (length 806)
                                                     (unsafe_get <fun>)))))))))
                                             (range
                                              ((start 550) (stop 553)
                                               (source
                                                (Reader
                                                 ((id 0) (name (expect_test.ml))
                                                  (length 806)
                                                  (unsafe_get <fun>)))))))
                                            ((it
                                              (Pat_var
                                               ((it exp)
                                                (range
                                                 ((start 555) (stop 558)
                                                  (source
                                                   (Reader
                                                    ((id 0)
                                                     (name (expect_test.ml))
                                                     (length 806)
                                                     (unsafe_get <fun>)))))))))
                                             (range
                                              ((start 555) (stop 558)
                                               (source
                                                (Reader
                                                 ((id 0) (name (expect_test.ml))
                                                  (length 806)
                                                  (unsafe_get <fun>))))))))))
                                         (range
                                          ((start 549) (stop 559)
                                           (source
                                            (Reader
                                             ((id 0) (name (expect_test.ml))
                                              (length 806) (unsafe_get <fun>)))))))
                                        ((it
                                          (Pat_var
                                           ((it env)
                                            (range
                                             ((start 560) (stop 563)
                                              (source
                                               (Reader
                                                ((id 0) (name (expect_test.ml))
                                                 (length 806) (unsafe_get <fun>)))))))))
                                         (range
                                          ((start 560) (stop 563)
                                           (source
                                            (Reader
                                             ((id 0) (name (expect_test.ml))
                                              (length 806) (unsafe_get <fun>))))))))
                                       ((it
                                         (Exp_app
                                          ((it
                                            (Exp_app
                                             ((it
                                               (Exp_app
                                                ((it
                                                  (Exp_var
                                                   ((it env_bind)
                                                    (range
                                                     ((start 581) (stop 589)
                                                      (source
                                                       (Reader
                                                        ((id 0)
                                                         (name (expect_test.ml))
                                                         (length 806)
                                                         (unsafe_get <fun>)))))))))
                                                 (range
                                                  ((start 581) (stop 589)
                                                   (source
                                                    (Reader
                                                     ((id 0)
                                                      (name (expect_test.ml))
                                                      (length 806)
                                                      (unsafe_get <fun>)))))))
                                                ((it
                                                  (Exp_var
                                                   ((it env)
                                                    (range
                                                     ((start 590) (stop 593)
                                                      (source
                                                       (Reader
                                                        ((id 0)
                                                         (name (expect_test.ml))
                                                         (length 806)
                                                         (unsafe_get <fun>)))))))))
                                                 (range
                                                  ((start 590) (stop 593)
                                                   (source
                                                    (Reader
                                                     ((id 0)
                                                      (name (expect_test.ml))
                                                      (length 806)
                                                      (unsafe_get <fun>)))))))))
                                              (range
                                               ((start 581) (stop 593)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))
                                             ((it
                                               (Exp_var
                                                ((it var)
                                                 (range
                                                  ((start 594) (stop 597)
                                                   (source
                                                    (Reader
                                                     ((id 0)
                                                      (name (expect_test.ml))
                                                      (length 806)
                                                      (unsafe_get <fun>)))))))))
                                              (range
                                               ((start 594) (stop 597)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))))
                                           (range
                                            ((start 581) (stop 597)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))
                                          ((it
                                            (Exp_var
                                             ((it exp)
                                              (range
                                               ((start 598) (stop 601)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))))
                                           (range
                                            ((start 598) (stop 601)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 581) (stop 601)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 545) (stop 601)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 806) (unsafe_get <fun>)))))))))
                                  (range
                                   ((start 515) (stop 602)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>))))))))))
                              (range
                               ((start 495) (stop 602)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             ((it
                               (Exp_app
                                ((it
                                  (Exp_app
                                   ((it
                                     (Exp_var
                                      ((it eval)
                                       (range
                                        ((start 627) (stop 631)
                                         (source
                                          (Reader
                                           ((id 0) (name (expect_test.ml))
                                            (length 806) (unsafe_get <fun>)))))))))
                                    (range
                                     ((start 627) (stop 631)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))
                                   ((it
                                     (Exp_var
                                      ((it env)
                                       (range
                                        ((start 632) (stop 635)
                                         (source
                                          (Reader
                                           ((id 0) (name (expect_test.ml))
                                            (length 806) (unsafe_get <fun>)))))))))
                                    (range
                                     ((start 632) (stop 635)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 627) (stop 635)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))
                                ((it
                                  (Exp_var
                                   ((it in_)
                                    (range
                                     ((start 636) (stop 639)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 636) (stop 639)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 627) (stop 639)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 492) (stop 639)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))))
                       (range
                        ((start 458) (stop 639)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>)))))))
                      ((it
                        ((case_lhs
                          ((it
                            (Pat_constr
                             ((it Bin_op)
                              (range
                               ((start 650) (stop 656)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             (((it
                                (Pat_tuple
                                 (((it
                                    (Pat_var
                                     ((it left)
                                      (range
                                       ((start 658) (stop 662)
                                        (source
                                         (Reader
                                          ((id 0) (name (expect_test.ml))
                                           (length 806) (unsafe_get <fun>)))))))))
                                   (range
                                    ((start 658) (stop 662)
                                     (source
                                      (Reader
                                       ((id 0) (name (expect_test.ml))
                                        (length 806) (unsafe_get <fun>)))))))
                                  ((it
                                    (Pat_var
                                     ((it op)
                                      (range
                                       ((start 664) (stop 666)
                                        (source
                                         (Reader
                                          ((id 0) (name (expect_test.ml))
                                           (length 806) (unsafe_get <fun>)))))))))
                                   (range
                                    ((start 664) (stop 666)
                                     (source
                                      (Reader
                                       ((id 0) (name (expect_test.ml))
                                        (length 806) (unsafe_get <fun>)))))))
                                  ((it
                                    (Pat_var
                                     ((it right)
                                      (range
                                       ((start 668) (stop 673)
                                        (source
                                         (Reader
                                          ((id 0) (name (expect_test.ml))
                                           (length 806) (unsafe_get <fun>)))))))))
                                   (range
                                    ((start 668) (stop 673)
                                     (source
                                      (Reader
                                       ((id 0) (name (expect_test.ml))
                                        (length 806) (unsafe_get <fun>))))))))))
                               (range
                                ((start 657) (stop 674)
                                 (source
                                  (Reader
                                   ((id 0) (name (expect_test.ml)) (length 806)
                                    (unsafe_get <fun>))))))))))
                           (range
                            ((start 650) (stop 674)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))
                         (case_rhs
                          ((it
                            (Exp_let
                             ((it
                               ((value_binding_var
                                 ((it n1)
                                  (range
                                   ((start 692) (stop 694)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>))))))))
                                (value_binding_over_flag Non_overloaded)
                                (value_binding_exp
                                 ((it
                                   (Exp_app
                                    ((it
                                      (Exp_app
                                       ((it
                                         (Exp_var
                                          ((it eval)
                                           (range
                                            ((start 697) (stop 701)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 697) (stop 701)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))
                                       ((it
                                         (Exp_var
                                          ((it env)
                                           (range
                                            ((start 702) (stop 705)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 702) (stop 705)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 697) (stop 705)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 806) (unsafe_get <fun>)))))))
                                    ((it
                                      (Exp_var
                                       ((it left)
                                        (range
                                         ((start 706) (stop 710)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 706) (stop 710)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 806) (unsafe_get <fun>)))))))))
                                  (range
                                   ((start 697) (stop 710)
                                    (source
                                     (Reader
                                      ((id 0) (name (expect_test.ml))
                                       (length 806) (unsafe_get <fun>))))))))))
                              (range
                               ((start 691) (stop 710)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))
                             ((it
                               (Exp_let
                                ((it
                                  ((value_binding_var
                                    ((it n2)
                                     (range
                                      ((start 728) (stop 730)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 806) (unsafe_get <fun>))))))))
                                   (value_binding_over_flag Non_overloaded)
                                   (value_binding_exp
                                    ((it
                                      (Exp_app
                                       ((it
                                         (Exp_app
                                          ((it
                                            (Exp_var
                                             ((it eval)
                                              (range
                                               ((start 733) (stop 737)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))))
                                           (range
                                            ((start 733) (stop 737)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))
                                          ((it
                                            (Exp_var
                                             ((it env)
                                              (range
                                               ((start 738) (stop 741)
                                                (source
                                                 (Reader
                                                  ((id 0) (name (expect_test.ml))
                                                   (length 806)
                                                   (unsafe_get <fun>)))))))))
                                           (range
                                            ((start 738) (stop 741)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 733) (stop 741)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))
                                       ((it
                                         (Exp_var
                                          ((it right)
                                           (range
                                            ((start 742) (stop 747)
                                             (source
                                              (Reader
                                               ((id 0) (name (expect_test.ml))
                                                (length 806) (unsafe_get <fun>)))))))))
                                        (range
                                         ((start 742) (stop 747)
                                          (source
                                           (Reader
                                            ((id 0) (name (expect_test.ml))
                                             (length 806) (unsafe_get <fun>)))))))))
                                     (range
                                      ((start 733) (stop 747)
                                       (source
                                        (Reader
                                         ((id 0) (name (expect_test.ml))
                                          (length 806) (unsafe_get <fun>))))))))))
                                 (range
                                  ((start 727) (stop 747)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))
                                ((it
                                  (Exp_app
                                   ((it
                                     (Exp_app
                                      ((it
                                        (Exp_app
                                         ((it
                                           (Exp_var
                                            ((it eval_bin_op)
                                             (range
                                              ((start 761) (stop 772)
                                               (source
                                                (Reader
                                                 ((id 0) (name (expect_test.ml))
                                                  (length 806)
                                                  (unsafe_get <fun>)))))))))
                                          (range
                                           ((start 761) (stop 772)
                                            (source
                                             (Reader
                                              ((id 0) (name (expect_test.ml))
                                               (length 806) (unsafe_get <fun>)))))))
                                         ((it
                                           (Exp_var
                                            ((it op)
                                             (range
                                              ((start 773) (stop 775)
                                               (source
                                                (Reader
                                                 ((id 0) (name (expect_test.ml))
                                                  (length 806)
                                                  (unsafe_get <fun>)))))))))
                                          (range
                                           ((start 773) (stop 775)
                                            (source
                                             (Reader
                                              ((id 0) (name (expect_test.ml))
                                               (length 806) (unsafe_get <fun>)))))))))
                                       (range
                                        ((start 761) (stop 775)
                                         (source
                                          (Reader
                                           ((id 0) (name (expect_test.ml))
                                            (length 806) (unsafe_get <fun>)))))))
                                      ((it
                                        (Exp_var
                                         ((it n1)
                                          (range
                                           ((start 776) (stop 778)
                                            (source
                                             (Reader
                                              ((id 0) (name (expect_test.ml))
                                               (length 806) (unsafe_get <fun>)))))))))
                                       (range
                                        ((start 776) (stop 778)
                                         (source
                                          (Reader
                                           ((id 0) (name (expect_test.ml))
                                            (length 806) (unsafe_get <fun>)))))))))
                                    (range
                                     ((start 761) (stop 778)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))
                                   ((it
                                     (Exp_var
                                      ((it n2)
                                       (range
                                        ((start 779) (stop 781)
                                         (source
                                          (Reader
                                           ((id 0) (name (expect_test.ml))
                                            (length 806) (unsafe_get <fun>)))))))))
                                    (range
                                     ((start 779) (stop 781)
                                      (source
                                       (Reader
                                        ((id 0) (name (expect_test.ml))
                                         (length 806) (unsafe_get <fun>)))))))))
                                 (range
                                  ((start 761) (stop 781)
                                   (source
                                    (Reader
                                     ((id 0) (name (expect_test.ml)) (length 806)
                                      (unsafe_get <fun>)))))))))
                              (range
                               ((start 724) (stop 781)
                                (source
                                 (Reader
                                  ((id 0) (name (expect_test.ml)) (length 806)
                                   (unsafe_get <fun>)))))))))
                           (range
                            ((start 688) (stop 781)
                             (source
                              (Reader
                               ((id 0) (name (expect_test.ml)) (length 806)
                                (unsafe_get <fun>))))))))))
                       (range
                        ((start 650) (stop 781)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 806)
                            (unsafe_get <fun>))))))))))
                   (range
                    ((start 378) (stop 791)
                     (source
                      (Reader
                       ((id 0) (name (expect_test.ml)) (length 806)
                        (unsafe_get <fun>)))))))))
                (range
                 ((start 350) (stop 791)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 806)
                     (unsafe_get <fun>)))))))))
             (range
              ((start 345) (stop 799)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))))
         (range
          ((start 337) (stop 799)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>)))))))))
      (range
       ((start 334) (stop 799)
        (source
         (Reader
          ((id 0) (name (expect_test.ml)) (length 806) (unsafe_get <fun>))))))))
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
    (((it
       (Str_primitive
        ((it
          ((value_name
            ((it greater_than)
             (range
              ((start 16) (stop 28)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>))))))))
           (value_type
            ((it
              ((scheme_quantifiers ())
               (scheme_body
                ((it
                  (Type_arrow
                   ((it
                     (Type_constr ()
                      ((it int)
                       (range
                        ((start 31) (stop 34)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 99)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 30) (stop 34)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 99)
                         (unsafe_get <fun>)))))))
                   ((it
                     (Type_arrow
                      ((it
                        (Type_constr ()
                         ((it int)
                          (range
                           ((start 38) (stop 41)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 99)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 37) (stop 41)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 99)
                            (unsafe_get <fun>)))))))
                      ((it
                        (Type_constr ()
                         ((it bool)
                          (range
                           ((start 45) (stop 49)
                            (source
                             (Reader
                              ((id 0) (name (expect_test.ml)) (length 99)
                               (unsafe_get <fun>)))))))))
                       (range
                        ((start 44) (stop 49)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 99)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 38) (stop 49)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 99)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 31) (stop 49)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 99)
                      (unsafe_get <fun>))))))))))
             (range
              ((start 31) (stop 49)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>))))))))))
         (range
          ((start 16) (stop 49)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>)))))))))
      (range
       ((start 7) (stop 49)
        (source
         (Reader ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>)))))))
     ((it
       (Str_primitive
        ((it
          ((value_name
            ((it to_sexp)
             (range
              ((start 68) (stop 75)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>))))))))
           (value_type
            ((it
              ((scheme_quantifiers
                (((it a)
                  (range
                   ((start 78) (stop 80)
                    (source
                     (Reader
                      ((id 0) (name (expect_test.ml)) (length 99)
                       (unsafe_get <fun>)))))))))
               (scheme_body
                ((it
                  (Type_arrow
                   ((it
                     (Type_var
                      ((it a)
                       (range
                        ((start 82) (stop 84)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 99)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 82) (stop 84)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 99)
                         (unsafe_get <fun>)))))))
                   ((it
                     (Type_constr ()
                      ((it sexp)
                       (range
                        ((start 88) (stop 92)
                         (source
                          (Reader
                           ((id 0) (name (expect_test.ml)) (length 99)
                            (unsafe_get <fun>)))))))))
                    (range
                     ((start 87) (stop 92)
                      (source
                       (Reader
                        ((id 0) (name (expect_test.ml)) (length 99)
                         (unsafe_get <fun>)))))))))
                 (range
                  ((start 82) (stop 92)
                   (source
                    (Reader
                     ((id 0) (name (expect_test.ml)) (length 99)
                      (unsafe_get <fun>))))))))))
             (range
              ((start 78) (stop 92)
               (source
                (Reader
                 ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>))))))))))
         (range
          ((start 68) (stop 92)
           (source
            (Reader
             ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>)))))))))
      (range
       ((start 59) (stop 92)
        (source
         (Reader ((id 0) (name (expect_test.ml)) (length 99) (unsafe_get <fun>))))))))
    |}]
;;

let%expect_test "no trailing ;;" =
  let str =
    {|
      let valid_function = fun () -> 1
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:3:5
      3 │
        │      ^
    |}]
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
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:4:9
      4 │          | A of int
        │          ^
    |}]
;;

let%expect_test "type definition - empty variant" =
  let str =
    {|
      type t = |;;
    |}
  in
  parse_and_print_structure str;
  [%expect
    {|
    error[E003]: syntax error
        ┌─ expect_test.ml:2:17
      2 │        type t = |;;
        │                  ^^
    |}]
;;
