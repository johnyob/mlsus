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
       (Match (matchee ((id 0) (name Type.Var))) (closure ((type_vars ())))
        (case <fun>) (else_ <fun>))))
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
    @@ match_ a1 ~closure:[ a1 ] ~with_:(fun _ -> T.var a1 =~ tint) ~else_:else_unsat_err
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Match (matchee ((id 0) (name Type.Var)))
        (closure ((type_vars (((id 0) (name Type.Var)))))) (case <fun>)
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
               | App (_, constr) ->
                 match_
                   constr
                   ~closure:[]
                   ~with_:(function
                     | Head (Constr constr) when T.Ident.(constr = tint_ident) -> tt
                     | _ -> ff unsat_err)
                   ~else_:else_unsat_err
               | _ -> ff unsat_err)
             ~else_:else_unsat_err)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (App (Spine ()) (Head (Constr ((id 0) (name int))))))
        (Match (matchee ((id 0) (name Type.Var))) (closure ((type_vars ())))
         (case <fun>) (else_ <fun>))))))
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
            | App (_, constr) ->
              match_
                constr
                ~closure:[]
                ~with_:(function
                  | Head (Constr constr) when T.Ident.(constr = tint_ident) -> tt
                  | _ -> ff unsat_err)
                ~else_:else_unsat_err
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
        (Match (matchee ((id 0) (name Type.Var))) (closure ((type_vars ())))
         (case <fun>) (else_ <fun>))
        (Eq (Var ((id 0) (name Type.Var)))
         (App (Spine ()) (Head (Constr ((id 0) (name int))))))))))
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
    @@ (match_ a1 ~closure:[ a2 ] ~with_:(fun _ -> T.var a2 =~ tint) ~else_:else_unsat_err
        &~ match_
             a2
             ~closure:[ a1 ]
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
          (closure ((type_vars (((id 1) (name Type.Var)))))) (case <fun>)
          (else_ <fun>))
         (Match (matchee ((id 1) (name Type.Var)))
          (closure ((type_vars (((id 0) (name Type.Var)))))) (case <fun>)
          (else_ <fun>))))))
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
             ~closure:[ a2 ]
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
          (Eq (Var ((id 0) (name Type.Var)))
           (App (Spine ()) (Head (Constr ((id 0) (name int))))))
          (Match (matchee ((id 0) (name Type.Var)))
           (closure ((type_vars (((id 1) (name Type.Var)))))) (case <fun>)
           (else_ <fun>)))
         (Match (matchee ((id 1) (name Type.Var))) (closure ((type_vars ())))
          (case <fun>) (else_ <fun>)))))))
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
              (App
               (Spine
                ((Var ((id 2) (name Type.Var))) (Var ((id 3) (name Type.Var)))))
               (Head Arrow)))
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
             (App
              (Spine
               ((Var ((id 5) (name Type.Var))) (Var ((id 0) (name Type.Var)))))
              (Head Arrow))))
           (Eq (Var ((id 5) (name Type.Var)))
            (App (Spine ()) (Head (Constr ((id 0) (name int)))))))))))))
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
                      ~closure:[ a3; a2 ]
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
             ((type_vars (((id 1) (name Type.Var)) ((id 2) (name Type.Var))))))
            (case <fun>) (else_ <fun>)))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Conj
          (Instance ((id 3) (name Constraint.Var))
           (App (Spine ()) (Head (Constr ((id 0) (name int))))))
          (Eq (Var ((id 0) (name Type.Var)))
           (App (Spine ()) (Head (Constr ((id 1) (name string))))))))))))
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
                      ~closure:[ a2 ]
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
           (closure ((type_vars (((id 1) (name Type.Var)))))) (case <fun>)
           (else_ <fun>)))
         (type_ (Var ((id 1) (name Type.Var)))))
        (Conj
         (Conj
          (Instance ((id 3) (name Constraint.Var))
           (App
            (Spine
             ((App (Spine ()) (Head (Constr ((id 0) (name int)))))
              (App (Spine ()) (Head (Constr ((id 0) (name int)))))))
            (Head Arrow)))
          (Instance ((id 3) (name Constraint.Var))
           (App
            (Spine
             ((App (Spine ()) (Head (Constr ((id 1) (name string)))))
              (App (Spine ()) (Head (Constr ((id 1) (name string)))))))
            (Head Arrow))))
         (Eq (Var ((id 0) (name Type.Var)))
          (App (Spine ()) (Head (Constr ((id 0) (name int)))))))))))
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
                     match_ a1 ~closure:[ a3 ] ~with_:(fun _ -> tt) ~else_:else_unsat_err
                     &~
                     (* This match is resolved after [a2] is unified with int.
                          But since [a3] is still partially generic, the structure of [a3] is
                          not propagated to [a4]. This causes a bug. *)
                     match_
                       a2
                       ~closure:[ a3 ]
                       ~with_:(fun _ -> T.(var a3 =~ tint))
                       ~else_:else_unsat_err)
                 @=> T.var a3))
         ~in_:
           (exists a4
            @@ (inst x1 (T.var a4)
                &~ T.(var a2 =~ tint)
                &~ match_
                     a4
                     ~closure:[ a1 ]
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
             (closure ((type_vars (((id 2) (name Type.Var)))))) (case <fun>)
             (else_ <fun>))
            (Match (matchee ((id 1) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))))) (case <fun>)
             (else_ <fun>))))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Exists ((id 3) (name Type.Var))
          (Conj
           (Conj
            (Instance ((id 4) (name Constraint.Var))
             (Var ((id 3) (name Type.Var))))
            (Eq (Var ((id 1) (name Type.Var)))
             (App (Spine ()) (Head (Constr ((id 0) (name int)))))))
           (Match (matchee ((id 3) (name Type.Var)))
            (closure ((type_vars (((id 0) (name Type.Var)))))) (case <fun>)
            (else_ <fun>)))))))))
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
        | App (spine, constr) ->
          match_
            spine
            ~closure:[ constr ]
            ~with_:(function
              | Spine [ t1; t2 ] ->
                match_
                  constr
                  ~closure:[ t1; t2 ]
                  ~with_:(function
                    | Head (Constr constr) when T.Ident.(constr = tapp_ident) ->
                      T.(var t1 =~ tapp (var t1) (var t2))
                    | _ -> ff unsat_err)
                  ~else_:else_unsat_err
              | _ -> ff unsat_err)
            ~else_:else_unsat_err
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
           (Match (matchee ((id 1) (name Type.Var))) (closure ((type_vars ())))
            (case <fun>) (else_ <fun>))
           (Match (matchee ((id 2) (name Type.Var))) (closure ((type_vars ())))
            (case <fun>) (else_ <fun>)))
          (Eq (Var ((id 1) (name Type.Var)))
           (App
            (Spine
             ((Var ((id 2) (name Type.Var))) (Var ((id 0) (name Type.Var)))))
            (Head (Constr ((id 2) (name app))))))))))))
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
                      ~closure:[ a3; a2 ]
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
             ((type_vars (((id 1) (name Type.Var)) ((id 2) (name Type.Var))))))
            (case <fun>) (else_ <fun>)))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Conj
          (Conj
           (Instance ((id 3) (name Constraint.Var))
            (App (Spine ()) (Head (Constr ((id 0) (name int))))))
           (Eq (Var ((id 1) (name Type.Var)))
            (App (Spine ()) (Head (Constr ((id 1) (name string)))))))
          (Eq (Var ((id 0) (name Type.Var)))
           (App (Spine ()) (Head (Constr ((id 0) (name int)))))))))))
     (err
      ((it
        (Cannot_unify (Var ((id 0) (name Decoded_type.Var)))
         (App (Spine ()) (Head (Constr ((id 1) (name string)))))))
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
                                   ~closure:[ a4; a3 ]
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
                ((type_vars (((id 2) (name Type.Var)) ((id 3) (name Type.Var))))))
               (case <fun>) (else_ <fun>)))
             (type_ (Var ((id 3) (name Type.Var)))))
            (Conj
             (Instance ((id 5) (name Constraint.Var))
              (App (Spine ()) (Head (Constr ((id 0) (name int))))))
             (Instance ((id 5) (name Constraint.Var))
              (App (Spine ()) (Head (Constr ((id 1) (name string)))))))))
          (type_ (Var ((id 2) (name Type.Var)))))
         (Eq (Var ((id 0) (name Type.Var)))
          (App (Spine ()) (Head (Constr ((id 1) (name string))))))))))
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
                      ~closure:[ a2; a3 ]
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
            ((type_vars (((id 1) (name Type.Var)) ((id 2) (name Type.Var))))))
           (case <fun>) (else_ <fun>)))
         (type_
          (App
           (Spine
            ((Var ((id 2) (name Type.Var))) (Var ((id 1) (name Type.Var)))))
           (Head Arrow))))
        (Exists ((id 3) (name Type.Var))
         (Exists ((id 4) (name Type.Var))
          (Conj
           (Conj
            (Conj
             (Instance ((id 5) (name Constraint.Var))
              (App
               (Spine
                ((Var ((id 3) (name Type.Var))) (Var ((id 4) (name Type.Var)))))
               (Head Arrow)))
             (Eq (Var ((id 3) (name Type.Var)))
              (App (Spine ()) (Head (Constr ((id 0) (name int)))))))
            (Eq (Var ((id 4) (name Type.Var)))
             (App (Spine ()) (Head (Constr ((id 1) (name string)))))))
           (Eq (Var ((id 0) (name Type.Var)))
            (App (Spine ()) (Head (Constr ((id 0) (name int))))))))))))
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
                 @. (match_ a2 ~closure:[ a3 ] ~with_:(fun _ -> tt) ~else_:else_unsat_err
                     &~ match_
                          a3
                          ~closure:[ a2 ]
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
             (closure ((type_vars (((id 2) (name Type.Var)))))) (case <fun>)
             (else_ <fun>))
            (Match (matchee ((id 2) (name Type.Var)))
             (closure ((type_vars (((id 1) (name Type.Var)))))) (case <fun>)
             (else_ <fun>)))
           (Eq (Var ((id 1) (name Type.Var))) (Var ((id 0) (name Type.Var))))))
         (type_
          (App
           (Spine
            ((Var ((id 1) (name Type.Var))) (Var ((id 2) (name Type.Var)))))
           (Head Arrow))))
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
