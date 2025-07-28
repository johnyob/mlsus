open Core
open Mlsus_std
open Mlsus_constraint
module C = Constraint
module T = C.Type

let () =
  let open Async.Log.Global in
  For_testing.use_test_output ()
;;

let unsat_err = Mlsus_error.bug_s ~here:[%here] [%message "Constraint is unsatisfiable"]

let else_unsat_err =
  let open C in
  fun () ->
    ff (Mlsus_error.bug_s ~here:[%here] [%message "Cannot resume due to generic/cycle"])
;;

let print_solve_result ?(log_level = `Info) cst =
  Async.Log.Global.set_level log_level;
  let result = Mlsus_constraint_solver.solve cst in
  match result with
  | Ok () -> print_s [%message "Constraint is satisfiable" (cst : Constraint.t)]
  | Error err ->
    print_s
      [%message
        "Constraint is unsatisfiable"
          (cst : Constraint.t)
          (err : Mlsus_constraint_solver.Error.t)]
;;

let predef_ident =
  let id_source = Identifier.create_source () in
  fun name -> T.Ident.create ~id_source ~name ()
;;

let tint_ident = predef_ident "int"
let tstring_ident = predef_ident "string"
let tint = T.constr [] tint_ident
let tstring = T.constr [] tstring_ident

let%expect_test "Cannot resume suspended generic" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let cst =
    exists a1 @@ match_ a1 ~closure:[] ~with_:(fun _ -> tt) ~else_:else_unsat_err
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Match (matchee ((id 0) (name Type.Var)))
        (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>))))
     (err
      ((it
        (Unsatisfiable
         ((severity Bug)
          (message
           "lib/constraint_solver/test/test_constraint_solver.ml:17:32: \"Cannot resume due to generic/cycle\"")
          (code (Unknown)) (labels ()) (notes ()))))
       (range ()))))
    |}]
;;

let%expect_test "Cannot unsuspend undetermined" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ match_
         a1
         ~closure:[ `Type a1 ]
         ~with_:(fun _ -> T.var a1 =~ tint)
         ~else_:else_unsat_err
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Match (matchee ((id 0) (name Type.Var)))
        (closure ((type_vars (((id 0) (name Type.Var)))) (vars ()))) (case <fun>)
        (else_ <fun>))))
     (err
      ((it
        (Unsatisfiable
         ((severity Bug)
          (message
           "lib/constraint_solver/test/test_constraint_solver.ml:17:32: \"Cannot resume due to generic/cycle\"")
          (code (Unknown)) (labels ()) (notes ()))))
       (range ()))))
    |}]
;;

let%expect_test "Can unsuspend determined (pre)" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ (T.(var a1 =~ tint)
        &~ match_
             a1
             ~closure:[]
             ~with_:(function
               | Constr (_, constr) when T.Ident.(constr = tint_ident) -> tt
               | _ -> ff unsat_err)
             ~else_:else_unsat_err)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))
        (Match (matchee ((id 0) (name Type.Var)))
         (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>))))))
    |}]
;;

let%expect_test "Can unsuspend determined (post)" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ (match_
          a1
          ~closure:[]
          ~with_:(function
            | Constr (_, constr) when T.Ident.(constr = tint_ident) -> tt
            | _ -> ff unsat_err)
          ~else_:else_unsat_err
        &~ T.(var a1 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Match (matchee ((id 0) (name Type.Var)))
         (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>))
        (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))))))
    |}]
;;

let%expect_test "Cannot unsuspend circular dependencies" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ exists a2
    @@ (match_
          a1
          ~closure:[ `Type a2 ]
          ~with_:(fun _ -> T.var a2 =~ tint)
          ~else_:else_unsat_err
        &~ match_
             a2
             ~closure:[ `Type a1 ]
             ~with_:(fun _ -> T.var a1 =~ tint)
             ~else_:else_unsat_err)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Conj
         (Match (matchee ((id 0) (name Type.Var)))
          (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
          (case <fun>) (else_ <fun>))
         (Match (matchee ((id 1) (name Type.Var)))
          (closure ((type_vars (((id 0) (name Type.Var)))) (vars ())))
          (case <fun>) (else_ <fun>))))))
     (err
      ((it
        (Unsatisfiable
         ((severity Bug)
          (message
           "lib/constraint_solver/test/test_constraint_solver.ml:17:32: \"Cannot resume due to generic/cycle\"")
          (code (Unknown)) (labels ()) (notes ()))))
       (range ()))))
    |}]
;;

let%expect_test "Can unsuspend topological dependencies" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ exists a2
    @@ (T.(var a1 =~ tint)
        &~ match_
             a1
             ~closure:[ `Type a2 ]
             ~with_:(fun _ -> T.var a2 =~ tint)
             ~else_:else_unsat_err
        &~ match_ a2 ~closure:[] ~with_:(fun _ -> tt) ~else_:else_unsat_err)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Conj
         (Conj
          (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))
          (Match (matchee ((id 0) (name Type.Var)))
           (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
           (case <fun>) (else_ <fun>)))
         (Match (matchee ((id 1) (name Type.Var)))
          (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)))))))
    |}]
;;

let%expect_test "No suspended matches results in normal generalization" =
  let open C in
  (* Example constraint is for the program:
     let id = fun x -> x in
     id 1
  *)
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let a4 = T.Var.create ~id_source () in
  let a5 = T.Var.create ~id_source () in
  let a6 = T.Var.create ~id_source () in
  let xid = Var.create ~id_source () in
  let xx = Var.create ~id_source () in
  let cst =
    exists a1
    @@ let_
         xid#=(poly_scheme
                 ([ Flexible, a2 ]
                  @. (exists a3
                      @@ exists a4
                      @@ (T.(var a2 =~ var a3 @-> var a4)
                          &~ let_ xx#=(mono_scheme (T.var a3)) ~in_:(inst xx (T.var a4)))
                     )
                  @=> T.var a2))
         ~in_:
           (exists a5
            @@ exists a6
            @@ (inst xid (T.var a5)
                &~ T.(var a5 =~ var a6 @-> var a1)
                &~ T.(var a6 =~ tint)))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 6) (name Constraint.Var))
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Exists ((id 2) (name Type.Var))
           (Exists ((id 3) (name Type.Var))
            (Conj
             (Eq (Var ((id 1) (name Type.Var)))
              (Arrow (Var ((id 2) (name Type.Var)))
               (Var ((id 3) (name Type.Var)))))
             (Let ((id 7) (name Constraint.Var))
              ((type_vars ()) (in_ True) (type_ (Var ((id 2) (name Type.Var)))))
              (Instance ((id 7) (name Constraint.Var))
               (Var ((id 3) (name Type.Var)))))))))
         (type_ (Var ((id 1) (name Type.Var)))))
        (Exists ((id 4) (name Type.Var))
         (Exists ((id 5) (name Type.Var))
          (Conj
           (Conj
            (Instance ((id 6) (name Constraint.Var))
             (Var ((id 4) (name Type.Var))))
            (Eq (Var ((id 4) (name Type.Var)))
             (Arrow (Var ((id 5) (name Type.Var)))
              (Var ((id 0) (name Type.Var))))))
           (Eq (Var ((id 5) (name Type.Var))) (Constr () ((id 0) (name int)))))))))))
    |}]
;;

let%expect_test "Partial generic becomes instance" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ exists a2
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a3 ]
                 @. match_
                      a1
                      ~closure:[ `Type a3; `Type a2 ]
                      ~with_:(fun _ -> T.(var a3 =~ var a2) &~ T.(var a2 =~ tint))
                      ~else_:else_unsat_err
                 @=> T.var a3))
         ~in_:(inst x1 tint &~ T.(var a1 =~ tstring))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let ((id 3) (name Constraint.Var))
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Match (matchee ((id 0) (name Type.Var)))
            (closure
             ((type_vars (((id 2) (name Type.Var)) ((id 1) (name Type.Var))))
              (vars ())))
            (case <fun>) (else_ <fun>)))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Conj
          (Instance ((id 3) (name Constraint.Var))
           (Constr () ((id 0) (name int))))
          (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 1) (name string))))))))))
    |}]
;;

let%expect_test "Partial generic becomes generic" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a2 ]
                 @. match_
                      a1
                      ~closure:[ `Type a2 ]
                      ~with_:(fun _ -> exists a3 @@ T.(var a2 =~ var a3 @-> var a3))
                      ~else_:else_unsat_err
                 @=> T.var a2))
         ~in_:
           (inst x1 T.(tint @-> tint)
            &~ inst x1 T.(tstring @-> tstring)
            &~ T.(var a1 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 3) (name Constraint.Var))
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Match (matchee ((id 0) (name Type.Var)))
           (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
           (case <fun>) (else_ <fun>)))
         (type_ (Var ((id 1) (name Type.Var)))))
        (Conj
         (Conj
          (Instance ((id 3) (name Constraint.Var))
           (Arrow (Constr () ((id 0) (name int)))
            (Constr () ((id 0) (name int)))))
          (Instance ((id 3) (name Constraint.Var))
           (Arrow (Constr () ((id 1) (name string)))
            (Constr () ((id 1) (name string))))))
         (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int)))))))))
    |}]
;;

let%expect_test "Propagating changes during partial generalization" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let a4 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists_many [ a1; a2 ]
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a3 ]
                 @. ((* This match forces [a3] to be partially generic *)
                     match_
                       a1
                       ~closure:[ `Type a3 ]
                       ~with_:(fun _ -> tt)
                       ~else_:else_unsat_err
                     &~
                     (* This match is resolved after [a2] is unified with int.
                          But since [a3] is still partially generic, the structure of [a3] is
                          not propagated to [a4]. This causes a bug. *)
                     match_
                       a2
                       ~closure:[ `Type a3 ]
                       ~with_:(fun _ -> T.(var a3 =~ tint))
                       ~else_:else_unsat_err)
                 @=> T.var a3))
         ~in_:
           (exists a4
            @@ (inst x1 (T.var a4)
                &~ T.(var a2 =~ tint)
                &~ match_
                     a4
                     ~closure:[ `Type a1 ]
                     ~with_:(fun _ -> T.(var a1 =~ tint))
                     ~else_:else_unsat_err))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let ((id 4) (name Constraint.Var))
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Conj
            (Match (matchee ((id 0) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>))
            (Match (matchee ((id 1) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>))))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Exists ((id 3) (name Type.Var))
          (Conj
           (Conj
            (Instance ((id 4) (name Constraint.Var))
             (Var ((id 3) (name Type.Var))))
            (Eq (Var ((id 1) (name Type.Var))) (Constr () ((id 0) (name int)))))
           (Match (matchee ((id 3) (name Type.Var)))
            (closure ((type_vars (((id 0) (name Type.Var)))) (vars ())))
            (case <fun>) (else_ <fun>)))))))))
    |}]
;;

let tapp_ident = predef_ident "app"
let tapp t1 t2 = T.constr [ t1; t2 ] tapp_ident

let%expect_test "loop" =
  let open C in
  let id_source = Identifier.create_source () in
  let omega alpha =
    match_
      alpha
      ~closure:[]
      ~with_:(function
        | Constr ([ t1; t2 ], constr) when T.Ident.(constr = tapp_ident) ->
          T.(var t1 =~ tapp (var t1) (var t2))
        | _ -> ff unsat_err)
      ~else_:else_unsat_err
  in
  let app e1 e2 alpha =
    let alpha1 = T.Var.create ~id_source () in
    let alpha2 = T.Var.create ~id_source () in
    exists_many
      [ alpha1; alpha2 ]
      (e1 alpha1 &~ e2 alpha2 &~ T.(var alpha1 =~ tapp (var alpha2) (var alpha)))
  in
  let beta = T.Var.create ~id_source () in
  let cst = exists beta @@ app omega omega beta in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Exists ((id 2) (name Type.Var))
         (Conj
          (Conj
           (Match (matchee ((id 1) (name Type.Var)))
            (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>))
           (Match (matchee ((id 2) (name Type.Var)))
            (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)))
          (Eq (Var ((id 1) (name Type.Var)))
           (Constr
            ((Var ((id 2) (name Type.Var))) (Var ((id 0) (name Type.Var))))
            ((id 2) (name app))))))))))
    |}]
;;

let%expect_test "Partial ungeneralization (Partial<>Instance)" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ exists a2
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a3 ]
                 @. match_
                      a1
                      ~closure:[ `Type a3; `Type a2 ]
                      ~with_:(fun _ -> T.(var a3 =~ var a2))
                      ~else_:else_unsat_err
                 @=> T.var a3))
         ~in_:(inst x1 tint &~ T.(var a2 =~ tstring) &~ T.(var a1 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let ((id 3) (name Constraint.Var))
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Match (matchee ((id 0) (name Type.Var)))
            (closure
             ((type_vars (((id 2) (name Type.Var)) ((id 1) (name Type.Var))))
              (vars ())))
            (case <fun>) (else_ <fun>)))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Conj
          (Conj
           (Instance ((id 3) (name Constraint.Var))
            (Constr () ((id 0) (name int))))
           (Eq (Var ((id 1) (name Type.Var))) (Constr () ((id 1) (name string)))))
          (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int)))))))))
     (err
      ((it
        (Cannot_unify (Var ((id 0) (name Decoded_type.Var)))
         (App (Spine ()) (Shape (Sh_constr 0 ((id 1) (name string)))))))
       (range ()))))
    |}]
;;

let%expect_test "Partial ungeneralization (Partial<>Partial)" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let a4 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let x2 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ exists a2
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a3 ]
                 @. let_
                      x2#=(poly_scheme
                             ([ Flexible, a4 ]
                              @. match_
                                   a1
                                   ~closure:[ `Type a4; `Type a3 ]
                                   ~with_:(fun _ -> T.(var a4 =~ var a3))
                                   ~else_:else_unsat_err
                              @=> T.var a4))
                      ~in_:(inst x2 tint &~ inst x2 tstring)
                 @=> T.var a3))
         ~in_:T.(var a1 =~ tstring)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let ((id 4) (name Constraint.Var))
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Let ((id 5) (name Constraint.Var))
            ((type_vars ((Flexible ((id 3) (name Type.Var)))))
             (in_
              (Match (matchee ((id 0) (name Type.Var)))
               (closure
                ((type_vars (((id 3) (name Type.Var)) ((id 2) (name Type.Var))))
                 (vars ())))
               (case <fun>) (else_ <fun>)))
             (type_ (Var ((id 3) (name Type.Var)))))
            (Conj
             (Instance ((id 5) (name Constraint.Var))
              (Constr () ((id 0) (name int))))
             (Instance ((id 5) (name Constraint.Var))
              (Constr () ((id 1) (name string)))))))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 1) (name string))))))))
     (err
      ((it
        (Cannot_unify (Var ((id 0) (name Decoded_type.Var)))
         (Var ((id 1) (name Decoded_type.Var)))))
       (range ()))))
    |}]
;;

let%expect_test "Partials propagate to same instance group" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let a4 = T.Var.create ~id_source () in
  let a5 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a2; Flexible, a3 ]
                 @. match_
                      a1
                      ~closure:[ `Type a2; `Type a3 ]
                      ~with_:(fun _ -> T.(var a2 =~ var a3))
                      ~else_:else_unsat_err
                 @=> T.(var a3 @-> var a2)))
         ~in_:
           (exists_many [ a4; a5 ]
            @@ (inst x1 T.(var a4 @-> var a5)
                &~ T.(var a4 =~ tint)
                &~ T.(var a5 =~ tstring)
                &~ T.(var a1 =~ tint)))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 5) (name Constraint.Var))
        ((type_vars
          ((Flexible ((id 1) (name Type.Var)))
           (Flexible ((id 2) (name Type.Var)))))
         (in_
          (Match (matchee ((id 0) (name Type.Var)))
           (closure
            ((type_vars (((id 1) (name Type.Var)) ((id 2) (name Type.Var))))
             (vars ())))
           (case <fun>) (else_ <fun>)))
         (type_
          (Arrow (Var ((id 2) (name Type.Var))) (Var ((id 1) (name Type.Var))))))
        (Exists ((id 3) (name Type.Var))
         (Exists ((id 4) (name Type.Var))
          (Conj
           (Conj
            (Conj
             (Instance ((id 5) (name Constraint.Var))
              (Arrow (Var ((id 3) (name Type.Var)))
               (Var ((id 4) (name Type.Var)))))
             (Eq (Var ((id 3) (name Type.Var))) (Constr () ((id 0) (name int)))))
            (Eq (Var ((id 4) (name Type.Var)))
             (Constr () ((id 1) (name string)))))
           (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))))))))
     (err
      ((it
        (Cannot_unify (Var ((id 0) (name Decoded_type.Var)))
         (Var ((id 1) (name Decoded_type.Var)))))
       (range ()))))
    |}]
;;

let%expect_test "Detect SCC cycle accross regions" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a2; Flexible, a3 ]
                 @. (match_
                       a2
                       ~closure:[ `Type a3 ]
                       ~with_:(fun _ -> tt)
                       ~else_:else_unsat_err
                     &~ match_
                          a3
                          ~closure:[ `Type a2 ]
                          ~with_:(fun _ -> tt)
                          ~else_:else_unsat_err
                     &~ T.(var a2 =~ var a1))
                 @=> T.(var a2 @-> var a3)))
         ~in_:tt
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 3) (name Constraint.Var))
        ((type_vars
          ((Flexible ((id 1) (name Type.Var)))
           (Flexible ((id 2) (name Type.Var)))))
         (in_
          (Conj
           (Conj
            (Match (matchee ((id 1) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>))
            (Match (matchee ((id 2) (name Type.Var)))
             (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>)))
           (Eq (Var ((id 1) (name Type.Var))) (Var ((id 0) (name Type.Var))))))
         (type_
          (Arrow (Var ((id 1) (name Type.Var))) (Var ((id 2) (name Type.Var))))))
        True)))
     (err
      ((it
        (Unsatisfiable
         ((severity Bug)
          (message
           "lib/constraint_solver/test/test_constraint_solver.ml:17:32: \"Cannot resume due to generic/cycle\"")
          (code (Unknown)) (labels ()) (notes ()))))
       (range ()))))
    |}]
;;

let%expect_test "" =
  (*
     Tests for a regression introduced here: https://github.com/johnyob/mlsus/pull/54
  
    1. Create partial generic ['a]
    2. Update the variable to ['a = 'b -> 'c] but the variables ['b, 'c] get generalized
    3. Try unify ['b, 'c] with [int]. This will try unify something with generic variables, 
       causing an [assert false]!
  *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let a3 = T.Var.create ~id_source () in
  let a4 = T.Var.create ~id_source () in
  let a5 = T.Var.create ~id_source () in
  let a6 = T.Var.create ~id_source () in
  let a7 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists_many [ a1; a5; a6; a7 ]
    @@ let_
         x1#=(poly_scheme
                ([ Flexible, a2 ]
                 @. (match_
                       a1
                       ~closure:[ `Type a2 ]
                       ~with_:(fun _ ->
                         exists_many [ a3; a4 ] @@ T.(var a2 =~ var a3 @-> var a4))
                       ~else_:else_unsat_err
                     &~ match_
                          a5
                          ~closure:[ `Type a2 ]
                          ~with_:(fun _ -> T.(var a2 =~ tint @-> tint))
                          ~else_:else_unsat_err)
                 @=> T.(var a2)))
         ~in_:
           ((* 1. Forces the generalization of x1's region *)
            inst x1 (T.var a6)
            (* 2. Schedule the first match handler, causes [a2] to be unified to [a3 -> a4] *)
            &~ T.(var a1 =~ tint)
            (* 3. Forces the re-generalization of x1's region *)
            &~ inst x1 (T.var a7)
            (* 4. Schedule the second match handler, causes [a2] to be unified to [int -> int] *)
            &~ T.(var a5 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 4) (name Type.Var))
        (Exists ((id 5) (name Type.Var))
         (Exists ((id 6) (name Type.Var))
          (Let ((id 7) (name Constraint.Var))
           ((type_vars ((Flexible ((id 1) (name Type.Var)))))
            (in_
             (Conj
              (Match (matchee ((id 0) (name Type.Var)))
               (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
               (case <fun>) (else_ <fun>))
              (Match (matchee ((id 4) (name Type.Var)))
               (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
               (case <fun>) (else_ <fun>))))
            (type_ (Var ((id 1) (name Type.Var)))))
           (Conj
            (Conj
             (Conj
              (Instance ((id 7) (name Constraint.Var))
               (Var ((id 5) (name Type.Var))))
              (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int)))))
             (Instance ((id 7) (name Constraint.Var))
              (Var ((id 6) (name Type.Var)))))
            (Eq (Var ((id 4) (name Type.Var))) (Constr () ((id 0) (name int))))))))))))
    |}]
;;

let%expect_test "" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let cst =
    exists a1
    @@ let_
         x1#=(poly_scheme @@ [ Flexible, a2 ] @. tt @=> T.(var a2 @-> var a2))
         ~in_:
           (match_
              a1
              ~closure:[ `Type a1; `Scheme x1 ]
              ~with_:(fun _ -> inst x1 (T.var a1))
              ~else_:else_unsat_err
            &~ T.(var a1 =~ tint @-> tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 2) (name Constraint.Var))
        ((type_vars ((Flexible ((id 1) (name Type.Var))))) (in_ True)
         (type_
          (Arrow (Var ((id 1) (name Type.Var))) (Var ((id 1) (name Type.Var))))))
        (Conj
         (Match (matchee ((id 0) (name Type.Var)))
          (closure
           ((type_vars (((id 0) (name Type.Var))))
            (vars (((id 2) (name Constraint.Var))))))
          (case <fun>) (else_ <fun>))
         (Eq (Var ((id 0) (name Type.Var)))
          (Arrow (Constr () ((id 0) (name int))) (Constr () ((id 0) (name int))))))))))
    |}]
;;

let%expect_test "" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let x2 = Var.create ~id_source () in
  let cst =
    exists_many [ a1 ]
    @@ let_
         x1#=(poly_scheme
              @@ [ Flexible, a2 ]
              @. let_
                   x2#=(mono_scheme (T.var a2))
                   ~in_:
                     (match_
                        a1
                        ~closure:[ `Scheme x2 ]
                        ~with_:(fun _ -> inst x2 tint)
                        ~else_:else_unsat_err)
              @=> T.var a2)
         ~in_:T.(var a1 =~ tint)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 2) (name Constraint.Var))
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Let ((id 3) (name Constraint.Var))
           ((type_vars ()) (in_ True) (type_ (Var ((id 1) (name Type.Var)))))
           (Match (matchee ((id 0) (name Type.Var)))
            (closure ((type_vars ()) (vars (((id 3) (name Constraint.Var))))))
            (case <fun>) (else_ <fun>))))
         (type_ (Var ((id 1) (name Type.Var)))))
        (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))))))
    |}]
;;

let%expect_test "" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let x1 = Var.create ~id_source () in
  let x2 = Var.create ~id_source () in
  let cst =
    exists_many [ a1 ]
    @@ let_
         x1#=(poly_scheme
              @@ [ Flexible, a2 ]
              @. let_
                   x2#=(mono_scheme (T.var a2))
                   ~in_:
                     (match_
                        a1
                        ~closure:[ `Scheme x2 ]
                        ~with_:(fun _ -> inst x2 tint)
                        ~else_:else_unsat_err)
              @=> T.var a2)
         ~in_:T.(var a1 =~ tint &~ inst x1 tstring)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let ((id 2) (name Constraint.Var))
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Let ((id 3) (name Constraint.Var))
           ((type_vars ()) (in_ True) (type_ (Var ((id 1) (name Type.Var)))))
           (Match (matchee ((id 0) (name Type.Var)))
            (closure ((type_vars ()) (vars (((id 3) (name Constraint.Var))))))
            (case <fun>) (else_ <fun>))))
         (type_ (Var ((id 1) (name Type.Var)))))
        (Conj (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))
         (Instance ((id 2) (name Constraint.Var))
          (Constr () ((id 1) (name string))))))))
     (err
      ((it
        (Cannot_unify (App (Spine ()) (Shape (Sh_constr 0 ((id 0) (name int)))))
         (App (Spine ()) (Shape (Sh_constr 0 ((id 1) (name string)))))))
       (range ()))))
    |}]
;;

let%expect_test "" =
  (* Basic alpha renaming *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let q2 = T.Var.create ~id_source () in
  let q3 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ T.(
         var a1
         =~ poly (Type_scheme.create ~quantifiers:[ q2 ] (var q2))
         &~ (var a1 =~ poly (Type_scheme.create ~quantifiers:[ q3 ] (var q3))))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 1) (name Type.Var))))
           (body (Var ((id 1) (name Type.Var)))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 2) (name Type.Var))))
           (body (Var ((id 2) (name Type.Var)))))))))))
    |}]
;;

let%expect_test "" =
  (* Ignoring useless polymorphism *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let q2 = T.Var.create ~id_source () in
  let q3 = T.Var.create ~id_source () in
  let q4 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ T.(
         var a1
         =~ poly (Type_scheme.create ~quantifiers:[ q2 ] (var q2))
         &~ (var a1 =~ poly (Type_scheme.create ~quantifiers:[ q3; q4 ] (var q3))))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 1) (name Type.Var))))
           (body (Var ((id 1) (name Type.Var)))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 2) (name Type.Var)) ((id 3) (name Type.Var))))
           (body (Var ((id 2) (name Type.Var)))))))))))
    |}]
;;

let%expect_test "" =
  (* 'a. 'a  and 'b.'b -> 'b should fail *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let q1 = T.Var.create ~id_source () in
  let q2 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ T.(
         var a1
         =~ poly (Type_scheme.create ~quantifiers:[ q1 ] (var q1))
         &~ (var a1 =~ poly (Type_scheme.create ~quantifiers:[ q2 ] (var q2 @-> var q2))))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 1) (name Type.Var))))
           (body (Var ((id 1) (name Type.Var)))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 2) (name Type.Var))))
           (body
            (Arrow (Var ((id 2) (name Type.Var))) (Var ((id 2) (name Type.Var)))))))))))
     (err
      ((it
        (Cannot_unify
         (App (Spine ())
          (Shape
           (Sh_poly
            ((quantifiers ())
             (scheme
              ((quantifiers (((id 0) (name Principal_shape.Var))))
               (body (Var ((id 0) (name Principal_shape.Var))))))))))
         (App (Spine ())
          (Shape
           (Sh_poly
            ((quantifiers ())
             (scheme
              ((quantifiers (((id 0) (name Principal_shape.Var))))
               (body
                (Arrow (Var ((id 0) (name Principal_shape.Var)))
                 (Var ((id 0) (name Principal_shape.Var)))))))))))))
       (range ()))))
    |}]
;;

let%expect_test "" =
  (* nested polytypes *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let q1 = T.Var.create ~id_source () in
  let q2 = T.Var.create ~id_source () in
  let q3 = T.Var.create ~id_source () in
  let q4 = T.Var.create ~id_source () in
  let poly1 =
    Type_scheme.create
      ~quantifiers:[ q1 ]
      T.(
        tuple
          [ var q1; poly (Type_scheme.create ~quantifiers:[ q2 ] (var q1 @-> var q2)) ])
  in
  let poly2 =
    Type_scheme.create
      ~quantifiers:[ q3 ]
      T.(
        tuple
          [ var q3; poly (Type_scheme.create ~quantifiers:[ q4 ] (var q3 @-> var q4)) ])
  in
  let cst = exists a1 @@ T.(var a1 =~ poly poly1 &~ (var a1 =~ poly poly2)) in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 1) (name Type.Var))))
           (body
            (Tuple
             ((Var ((id 1) (name Type.Var)))
              (Poly
               ((quantifiers (((id 2) (name Type.Var))))
                (body
                 (Arrow (Var ((id 1) (name Type.Var)))
                  (Var ((id 2) (name Type.Var)))))))))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Poly
          ((quantifiers (((id 3) (name Type.Var))))
           (body
            (Tuple
             ((Var ((id 3) (name Type.Var)))
              (Poly
               ((quantifiers (((id 4) (name Type.Var))))
                (body
                 (Arrow (Var ((id 3) (name Type.Var)))
                  (Var ((id 4) (name Type.Var)))))))))))))))))
    |}]
;;

let%expect_test "" =
  (* monomorphism in polytypes *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let q1 = T.Var.create ~id_source () in
  let cst =
    exists_many [ a1; a2 ]
    @@ T.(
         var a1
         =~ poly (Type_scheme.create ~quantifiers:[ q1 ] (tint @-> var q1))
         &~ (var a1 =~ poly (Type_scheme.create ~quantifiers:[ q1 ] (var a2 @-> var q1)))
         &~ (var a2 =~ tstring))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Conj
         (Conj
          (Eq (Var ((id 0) (name Type.Var)))
           (Poly
            ((quantifiers (((id 2) (name Type.Var))))
             (body
              (Arrow (Constr () ((id 0) (name int)))
               (Var ((id 2) (name Type.Var))))))))
          (Eq (Var ((id 0) (name Type.Var)))
           (Poly
            ((quantifiers (((id 2) (name Type.Var))))
             (body
              (Arrow (Var ((id 1) (name Type.Var)))
               (Var ((id 2) (name Type.Var)))))))))
         (Eq (Var ((id 1) (name Type.Var))) (Constr () ((id 1) (name string))))))))
     (err
      ((it
        (Cannot_unify (App (Spine ()) (Shape (Sh_constr 0 ((id 0) (name int)))))
         (App (Spine ()) (Shape (Sh_constr 0 ((id 1) (name string)))))))
       (range ()))))
    |}]
;;
