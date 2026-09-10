open Core
open Omniml_std
module C = Omniml_constraint_solver.Constraint
module T = Omniml_constraint_solver.Type

let () =
  let open Omniml_log.Global in
  For_testing.use_test_output ()
;;

let solve ?(defaulting = false) ?(log_level = `Info) cst =
  Omniml_log.Global.set_level log_level;
  let options = Omniml_options.(empty |> with_ ~option:Defaulting ~enabled:defaulting) in
  Omniml_constraint_solver.solve ~options cst
;;

let unsat_err = Omniml_error.bug_s ~here:[%here] [%message "Constraint is unsatisfiable"]

let match_err _ =
  Omniml_error.bug_s ~here:[%here] [%message "Cannot resume due to generic/cycle"]
;;

let default_match_err () = C.(Constraint (ff (match_err ())))

let print_solve_result ?defaulting ?log_level cst =
  let cst = C.map cst ~f:(fun _ -> ()) in
  let result = solve ?defaulting ?log_level cst in
  match result with
  | Ok () -> print_s [%message "Constraint is satisfiable" (cst : C.t)]
  | Error err ->
    print_s
      [%message
        "Constraint is unsatisfiable" (cst : C.t) (err : Omniml_constraint_solver.Error.t)]
;;

let predef_ident =
  let id_source = Identifier.create_source () in
  fun name -> T.Ident.create ~id_source ~name ()
;;

let tint_ident = predef_ident "int"
let tstring_ident = predef_ident "string"
let tint = T.constr [] tint_ident
let tstring = T.constr [] tstring_ident

let%expect_test "handler scheduling is not re-entrant" =
  let module Scheduler = Omniml_constraint_solver.For_testing.Scheduler in
  let scheduler = Scheduler.create () in
  let event name = print_endline name in
  Scheduler.enqueue_handler scheduler (fun () ->
    event "first: begin";
    Scheduler.enqueue_handler scheduler (fun () -> event "second");
    Scheduler.enqueue scheduler (fun () -> event "maintenance");
    Scheduler.run scheduler;
    event "first: end");
  Scheduler.run scheduler;
  [%expect
    {|
    first: begin
    maintenance
    first: end
    second
    |}]
;;

let%expect_test "Applicative constraints return values" =
  let open C.Let_syntax in
  let cst =
    let%map lhs = C.return 20
    and rhs = C.return 22 in
    lhs + rhs
  in
  print_s [%sexp (solve cst : (int, _) Result.t)];
  [%expect {| (Ok 42) |}]
;;

let%expect_test "Decode observes the final solution" =
  let open C in
  let open C.Let_syntax in
  let id_source = Identifier.create_source () in
  let type_var = T.Var.create ~id_source () in
  let cst =
    exists type_var
    @@
    let%map () = T.(var type_var =~ tint)
    and decoded = decode (T.var type_var) in
    decoded
  in
  (match solve cst with
   | Ok decoded -> Fmt.pr "%a@." Omniml_typed_ast.Typed_ast.Type.pp decoded
   | Error _ -> print_endline "error");
  [%expect {| int |}]
;;

let%expect_test "Semantic actions do not run after failure" =
  let ran = ref false in
  let cst = C.map (C.ff unsat_err) ~f:(fun () -> ran := true) in
  ignore (solve cst : (unit, _) Result.t);
  print_s [%sexp (!ran : bool)];
  [%expect {| false |}]
;;

let%expect_test "Let constraints preserve both values" =
  let open C in
  let binding = poly_binding ([] @. return 20 @=> []) in
  print_s [%sexp (solve (let_ binding ~in_:(return 22)) : (int * int, _) Result.t)];
  [%expect {| (Ok (20 22)) |}]
;;

let%expect_test "Cannot resume suspended generic" =
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let cst =
    exists a1
    @@ match_
         a1
         ~closure:[]
         ~with_:(fun _ -> tt)
         ~default:default_match_err
         ~error:match_err
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Match (matchee ((id 0) (name Type.Var)))
        (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
        (error <fun>))))
     (err
      ((it
        (Cannot_discharge_match_constraints
         ((((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ()))))))
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
         ~default:default_match_err
         ~error:match_err
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Match (matchee ((id 0) (name Type.Var)))
        (closure ((type_vars (((id 0) (name Type.Var)))) (vars ()))) (case <fun>)
        (else_ <fun>) (error <fun>))))
     (err
      ((it
        (Cannot_discharge_match_constraints
         ((((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ()))))))
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
        >> match_
             a1
             ~closure:[]
             ~with_:(function
               | Constr (_, constr) when T.Ident.(constr = tint_ident) -> tt
               | _ -> ff unsat_err)
             ~default:default_match_err
             ~error:match_err)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))
        (Match (matchee ((id 0) (name Type.Var)))
         (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
         (error <fun>))))))
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
          ~default:default_match_err
          ~error:match_err
        >> T.(var a1 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Match (matchee ((id 0) (name Type.Var)))
         (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
         (error <fun>))
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
          ~default:default_match_err
          ~error:match_err
        >> match_
             a2
             ~closure:[ `Type a1 ]
             ~with_:(fun _ -> T.var a1 =~ tint)
             ~default:default_match_err
             ~error:match_err)
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
          (case <fun>) (else_ <fun>) (error <fun>))
         (Match (matchee ((id 1) (name Type.Var)))
          (closure ((type_vars (((id 0) (name Type.Var)))) (vars ())))
          (case <fun>) (else_ <fun>) (error <fun>))))))
     (err
      ((it
        (Cannot_discharge_match_constraints
         ((((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ())))
          (((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ()))))))
       (range ()))))
    |}]
;;

let default_int_shape () =
  C.Shape (Omniml_constraint_solver.Principal_shape.constr ~arity:0 tint_ident)
;;

let%expect_test "a trivial defaulting dependency does not prevent defaulting" =
  let open C in
  let id_source = Identifier.create_source () in
  let a = T.Var.create ~id_source () in
  let cst =
    exists a
    @@ match_
         a
         ~closure:[]
         ~with_:(fun _ -> tt)
         ~default:default_int_shape
         ~error:match_err
  in
  print_solve_result ~defaulting:true cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Match (matchee ((id 0) (name Type.Var)))
        (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
        (error <fun>)))))
    |}]
;;

let%expect_test "a non-trivial defaulting cycle prevents defaulting" =
  let open C in
  let id_source = Identifier.create_source () in
  let a = T.Var.create ~id_source () in
  let b = T.Var.create ~id_source () in
  let cst =
    exists a
    @@ exists b
    @@ (match_
          a
          ~closure:[ `Type b ]
          ~with_:(fun _ -> tt)
          ~default:default_int_shape
          ~error:match_err
        >> match_
             b
             ~closure:[ `Type a ]
             ~with_:(fun _ -> tt)
             ~default:default_int_shape
             ~error:match_err)
  in
  print_solve_result ~defaulting:true cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Conj
         (Match (matchee ((id 0) (name Type.Var)))
          (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
          (case <fun>) (else_ <fun>) (error <fun>))
         (Match (matchee ((id 1) (name Type.Var)))
          (closure ((type_vars (((id 0) (name Type.Var)))) (vars ())))
          (case <fun>) (else_ <fun>) (error <fun>))))))
     (err
      ((it
        (Cannot_discharge_match_constraints
         ((((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ())))
          (((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ()))))))
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
        >> match_
             a1
             ~closure:[ `Type a2 ]
             ~with_:(fun _ -> T.var a2 =~ tint)
             ~default:default_match_err
             ~error:match_err
        >> match_
             a2
             ~closure:[]
             ~with_:(fun _ -> tt)
             ~default:default_match_err
             ~error:match_err)
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
           (case <fun>) (else_ <fun>) (error <fun>)))
         (Match (matchee ((id 1) (name Type.Var)))
          (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
          (error <fun>)))))))
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
         (poly_binding
            ([ Flexible, a2 ]
             @. (exists a3
                 @@ exists a4
                 @@ (T.(var a2 =~ var a3 @-> var a4)
                     >> let_ (mono_binding [ xx @: T.var a3 ]) ~in_:(inst xx (T.var a4)))
                )
             @=> [ xid @: T.var a2 ]))
         ~in_:
           (exists a5
            @@ exists a6
            @@ (inst xid (T.var a5)
                >> T.(var a5 =~ var a6 @-> var a1)
                >> T.(var a6 =~ tint)))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Exists ((id 2) (name Type.Var))
           (Exists ((id 3) (name Type.Var))
            (Conj
             (Eq (Var ((id 1) (name Type.Var)))
              (Arrow (Var ((id 2) (name Type.Var)))
               (Var ((id 3) (name Type.Var)))))
             (Let
              ((type_vars ()) (in_ True)
               (bindings
                (((binding_var ((id 7) (name Constraint.Var)))
                  (binding_type (Var ((id 2) (name Type.Var))))))))
              (Instance ((id 7) (name Constraint.Var))
               (Var ((id 3) (name Type.Var)))))))))
         (bindings
          (((binding_var ((id 6) (name Constraint.Var)))
            (binding_type (Var ((id 1) (name Type.Var))))))))
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
         (poly_binding
            ([ Flexible, a3 ]
             @. match_
                  a1
                  ~closure:[ `Type a3; `Type a2 ]
                  ~with_:(fun _ -> T.(var a3 =~ var a2) >> T.(var a2 =~ tint))
                  ~default:default_match_err
                  ~error:match_err
             @=> [ x1 @: T.var a3 ]))
         ~in_:(inst x1 tint >> T.(var a1 =~ tstring))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Match (matchee ((id 0) (name Type.Var)))
            (closure
             ((type_vars (((id 2) (name Type.Var)) ((id 1) (name Type.Var))))
              (vars ())))
            (case <fun>) (else_ <fun>) (error <fun>)))
          (bindings
           (((binding_var ((id 3) (name Constraint.Var)))
             (binding_type (Var ((id 2) (name Type.Var))))))))
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
         (poly_binding
            ([ Flexible, a2 ]
             @. match_
                  a1
                  ~closure:[ `Type a2 ]
                  ~with_:(fun _ -> exists a3 @@ T.(var a2 =~ var a3 @-> var a3))
                  ~default:default_match_err
                  ~error:match_err
             @=> [ x1 @: T.var a2 ]))
         ~in_:
           (inst x1 T.(tint @-> tint)
            >> inst x1 T.(tstring @-> tstring)
            >> T.(var a1 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Match (matchee ((id 0) (name Type.Var)))
           (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
           (case <fun>) (else_ <fun>) (error <fun>)))
         (bindings
          (((binding_var ((id 3) (name Constraint.Var)))
            (binding_type (Var ((id 1) (name Type.Var))))))))
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
         (poly_binding
            ([ Flexible, a3 ]
             @. ((* This match forces [a3] to be partially generic *)
                 match_
                   a1
                   ~closure:[ `Type a3 ]
                   ~with_:(fun _ -> tt)
                   ~default:default_match_err
                   ~error:match_err
                 >>
                 (* This match is resolved after [a2] is unified with int.
                          But since [a3] is still partially generic, the structure of [a3] is
                          not propagated to [a4]. This causes a bug. *)
                 match_
                   a2
                   ~closure:[ `Type a3 ]
                   ~with_:(fun _ -> T.(var a3 =~ tint))
                   ~default:default_match_err
                   ~error:match_err)
             @=> [ x1 @: T.var a3 ]))
         ~in_:
           (exists a4
            @@ (inst x1 (T.var a4)
                >> T.(var a2 =~ tint)
                >> match_
                     a4
                     ~closure:[ `Type a1 ]
                     ~with_:(fun _ -> T.(var a1 =~ tint))
                     ~default:default_match_err
                     ~error:match_err))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Conj
            (Match (matchee ((id 0) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>) (error <fun>))
            (Match (matchee ((id 1) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>) (error <fun>))))
          (bindings
           (((binding_var ((id 4) (name Constraint.Var)))
             (binding_type (Var ((id 2) (name Type.Var))))))))
         (Exists ((id 3) (name Type.Var))
          (Conj
           (Conj
            (Instance ((id 4) (name Constraint.Var))
             (Var ((id 3) (name Type.Var))))
            (Eq (Var ((id 1) (name Type.Var))) (Constr () ((id 0) (name int)))))
           (Match (matchee ((id 3) (name Type.Var)))
            (closure ((type_vars (((id 0) (name Type.Var)))) (vars ())))
            (case <fun>) (else_ <fun>) (error <fun>)))))))))
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
      ~default:default_match_err
      ~error:match_err
  in
  let app e1 e2 alpha =
    let alpha1 = T.Var.create ~id_source () in
    let alpha2 = T.Var.create ~id_source () in
    exists_many
      [ alpha1; alpha2 ]
      (e1 alpha1 >> e2 alpha2 >> T.(var alpha1 =~ tapp (var alpha2) (var alpha)))
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
            (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
            (error <fun>))
           (Match (matchee ((id 2) (name Type.Var)))
            (closure ((type_vars ()) (vars ()))) (case <fun>) (else_ <fun>)
            (error <fun>)))
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
         (poly_binding
            ([ Flexible, a3 ]
             @. match_
                  a1
                  ~closure:[ `Type a3; `Type a2 ]
                  ~with_:(fun _ -> T.(var a3 =~ var a2))
                  ~default:default_match_err
                  ~error:match_err
             @=> [ x1 @: T.var a3 ]))
         ~in_:(inst x1 tint >> T.(var a2 =~ tstring) >> T.(var a1 =~ tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Match (matchee ((id 0) (name Type.Var)))
            (closure
             ((type_vars (((id 2) (name Type.Var)) ((id 1) (name Type.Var))))
              (vars ())))
            (case <fun>) (else_ <fun>) (error <fun>)))
          (bindings
           (((binding_var ((id 3) (name Constraint.Var)))
             (binding_type (Var ((id 2) (name Type.Var))))))))
         (Conj
          (Conj
           (Instance ((id 3) (name Constraint.Var))
            (Constr () ((id 0) (name int))))
           (Eq (Var ((id 1) (name Type.Var))) (Constr () ((id 1) (name string)))))
          (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int)))))))))
     (err
      ((it
        (Cannot_unify (Constr () ((id 1) (name string)))
         (Constr () ((id 0) (name int)))))
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
         (poly_binding
            ([ Flexible, a3 ]
             @. let_
                  (poly_binding
                     ([ Flexible, a4 ]
                      @. match_
                           a1
                           ~closure:[ `Type a4; `Type a3 ]
                           ~with_:(fun _ -> T.(var a4 =~ var a3))
                           ~default:default_match_err
                           ~error:match_err
                      @=> [ x2 @: T.var a4 ]))
                  ~in_:(inst x2 tint >> inst x2 tstring)
             @=> [ x1 @: T.var a3 ]))
         ~in_:T.(var a1 =~ tstring)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Exists ((id 1) (name Type.Var))
        (Let
         ((type_vars ((Flexible ((id 2) (name Type.Var)))))
          (in_
           (Let
            ((type_vars ((Flexible ((id 3) (name Type.Var)))))
             (in_
              (Match (matchee ((id 0) (name Type.Var)))
               (closure
                ((type_vars (((id 3) (name Type.Var)) ((id 2) (name Type.Var))))
                 (vars ())))
               (case <fun>) (else_ <fun>) (error <fun>)))
             (bindings
              (((binding_var ((id 5) (name Constraint.Var)))
                (binding_type (Var ((id 3) (name Type.Var))))))))
            (Conj
             (Instance ((id 5) (name Constraint.Var))
              (Constr () ((id 0) (name int))))
             (Instance ((id 5) (name Constraint.Var))
              (Constr () ((id 1) (name string)))))))
          (bindings
           (((binding_var ((id 4) (name Constraint.Var)))
             (binding_type (Var ((id 2) (name Type.Var))))))))
         (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 1) (name string))))))))
     (err
      ((it
        (Cannot_unify (Constr () ((id 0) (name int)))
         (Constr () ((id 1) (name string)))))
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
         (poly_binding
            ([ Flexible, a2; Flexible, a3 ]
             @. match_
                  a1
                  ~closure:[ `Type a2; `Type a3 ]
                  ~with_:(fun _ -> T.(var a2 =~ var a3))
                  ~default:default_match_err
                  ~error:match_err
             @=> [ (x1 @: T.(var a3 @-> var a2)) ]))
         ~in_:
           (exists_many [ a4; a5 ]
            @@ (inst x1 T.(var a4 @-> var a5)
                >> T.(var a4 =~ tint)
                >> T.(var a5 =~ tstring)
                >> T.(var a1 =~ tint)))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars
          ((Flexible ((id 1) (name Type.Var)))
           (Flexible ((id 2) (name Type.Var)))))
         (in_
          (Match (matchee ((id 0) (name Type.Var)))
           (closure
            ((type_vars (((id 1) (name Type.Var)) ((id 2) (name Type.Var))))
             (vars ())))
           (case <fun>) (else_ <fun>) (error <fun>)))
         (bindings
          (((binding_var ((id 5) (name Constraint.Var)))
            (binding_type
             (Arrow (Var ((id 2) (name Type.Var)))
              (Var ((id 1) (name Type.Var)))))))))
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
         (poly_binding
            ([ Flexible, a2; Flexible, a3 ]
             @. (match_
                   a2
                   ~closure:[ `Type a3 ]
                   ~with_:(fun _ -> tt)
                   ~default:default_match_err
                   ~error:match_err
                 >> match_
                      a3
                      ~closure:[ `Type a2 ]
                      ~with_:(fun _ -> tt)
                      ~default:default_match_err
                      ~error:match_err
                 >> T.(var a2 =~ var a1))
             @=> [ (x1 @: T.(var a2 @-> var a3)) ]))
         ~in_:tt
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars
          ((Flexible ((id 1) (name Type.Var)))
           (Flexible ((id 2) (name Type.Var)))))
         (in_
          (Conj
           (Conj
            (Match (matchee ((id 1) (name Type.Var)))
             (closure ((type_vars (((id 2) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>) (error <fun>))
            (Match (matchee ((id 2) (name Type.Var)))
             (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
             (case <fun>) (else_ <fun>) (error <fun>)))
           (Eq (Var ((id 1) (name Type.Var))) (Var ((id 0) (name Type.Var))))))
         (bindings
          (((binding_var ((id 3) (name Constraint.Var)))
            (binding_type
             (Arrow (Var ((id 1) (name Type.Var)))
              (Var ((id 2) (name Type.Var)))))))))
        True)))
     (err
      ((it
        (Cannot_discharge_match_constraints
         ((((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ())))
          (((severity Bug)
            (message
             "lib/constraint_solver/test/test_constraint_solver.ml:20:27: \"Cannot resume due to generic/cycle\"")
            (code (Unknown)) (labels ()) (notes ()))))))
       (range ()))))
    |}]
;;

let%expect_test "" =
  (*
     Tests for a regression introduced here: https://github.com/johnyob/omniml/pull/54
  
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
         (poly_binding
            ([ Flexible, a2 ]
             @. (match_
                   a1
                   ~closure:[ `Type a2 ]
                   ~with_:(fun _ ->
                     exists_many [ a3; a4 ] @@ T.(var a2 =~ var a3 @-> var a4))
                   ~default:default_match_err
                   ~error:match_err
                 >> match_
                      a5
                      ~closure:[ `Type a2 ]
                      ~with_:(fun _ -> T.(var a2 =~ tint @-> tint))
                      ~default:default_match_err
                      ~error:match_err)
             @=> [ x1 @: T.var a2 ]))
         ~in_:
           ((* 1. Forces the generalization of x1's region *)
            inst x1 (T.var a6)
            (* 2. Schedule the first match handler, causes [a2] to be unified to [a3 -> a4] *)
            >> T.(var a1 =~ tint)
            (* 3. Forces the re-generalization of x1's region *)
            >> inst x1 (T.var a7)
            (* 4. Schedule the second match handler, causes [a2] to be unified to [int -> int] *)
            >> T.(var a5 =~ tint))
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
          (Let
           ((type_vars ((Flexible ((id 1) (name Type.Var)))))
            (in_
             (Conj
              (Match (matchee ((id 0) (name Type.Var)))
               (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
               (case <fun>) (else_ <fun>) (error <fun>))
              (Match (matchee ((id 4) (name Type.Var)))
               (closure ((type_vars (((id 1) (name Type.Var)))) (vars ())))
               (case <fun>) (else_ <fun>) (error <fun>))))
            (bindings
             (((binding_var ((id 7) (name Constraint.Var)))
               (binding_type (Var ((id 1) (name Type.Var))))))))
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
         (poly_binding @@ [ Flexible, a2 ] @. tt @=> [ (x1 @: T.(var a2 @-> var a2)) ])
         ~in_:
           (match_
              a1
              ~closure:[ `Type a1; `Scheme x1 ]
              ~with_:(fun _ -> inst x1 (T.var a1))
              ~default:default_match_err
              ~error:match_err
            >> T.(var a1 =~ tint @-> tint))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars ((Flexible ((id 1) (name Type.Var))))) (in_ True)
         (bindings
          (((binding_var ((id 2) (name Constraint.Var)))
            (binding_type
             (Arrow (Var ((id 1) (name Type.Var)))
              (Var ((id 1) (name Type.Var)))))))))
        (Conj
         (Match (matchee ((id 0) (name Type.Var)))
          (closure
           ((type_vars (((id 0) (name Type.Var))))
            (vars (((id 2) (name Constraint.Var))))))
          (case <fun>) (else_ <fun>) (error <fun>))
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
         (poly_binding
          @@ [ Flexible, a2 ]
          @. let_
               (mono_binding [ x2 @: T.var a2 ])
               ~in_:
                 (match_
                    a1
                    ~closure:[ `Scheme x2 ]
                    ~with_:(fun _ -> inst x2 tint)
                    ~default:default_match_err
                    ~error:match_err)
          @=> [ x1 @: T.var a2 ])
         ~in_:T.(var a1 =~ tint)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Let
           ((type_vars ()) (in_ True)
            (bindings
             (((binding_var ((id 3) (name Constraint.Var)))
               (binding_type (Var ((id 1) (name Type.Var))))))))
           (Match (matchee ((id 0) (name Type.Var)))
            (closure ((type_vars ()) (vars (((id 3) (name Constraint.Var))))))
            (case <fun>) (else_ <fun>) (error <fun>))))
         (bindings
          (((binding_var ((id 2) (name Constraint.Var)))
            (binding_type (Var ((id 1) (name Type.Var))))))))
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
         (poly_binding
          @@ [ Flexible, a2 ]
          @. let_
               (mono_binding [ x2 @: T.var a2 ])
               ~in_:
                 (match_
                    a1
                    ~closure:[ `Scheme x2 ]
                    ~with_:(fun _ -> inst x2 tint)
                    ~default:default_match_err
                    ~error:match_err)
          @=> [ x1 @: T.var a2 ])
         ~in_:T.(var a1 =~ tint >> inst x1 tstring)
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Let
        ((type_vars ((Flexible ((id 1) (name Type.Var)))))
         (in_
          (Let
           ((type_vars ()) (in_ True)
            (bindings
             (((binding_var ((id 3) (name Constraint.Var)))
               (binding_type (Var ((id 1) (name Type.Var))))))))
           (Match (matchee ((id 0) (name Type.Var)))
            (closure ((type_vars ()) (vars (((id 3) (name Constraint.Var))))))
            (case <fun>) (else_ <fun>) (error <fun>))))
         (bindings
          (((binding_var ((id 2) (name Constraint.Var)))
            (binding_type (Var ((id 1) (name Type.Var))))))))
        (Conj (Eq (Var ((id 0) (name Type.Var))) (Constr () ((id 0) (name int))))
         (Instance ((id 2) (name Constraint.Var))
          (Constr () ((id 1) (name string))))))))
     (err
      ((it
        (Cannot_unify (Constr () ((id 0) (name int)))
         (Constr () ((id 1) (name string)))))
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
         =~ scheme (T.Scheme.create ~quantifiers:[ q2 ] (var q2))
         >> (var a1 =~ scheme (T.Scheme.create ~quantifiers:[ q3 ] (var q3))))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
          ((quantifiers (((id 1) (name Type.Var))))
           (body (Var ((id 1) (name Type.Var)))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
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
         =~ scheme (T.Scheme.create ~quantifiers:[ q2 ] (var q2))
         >> (var a1 =~ scheme (T.Scheme.create ~quantifiers:[ q3; q4 ] (var q3))))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
          ((quantifiers (((id 1) (name Type.Var))))
           (body (Var ((id 1) (name Type.Var)))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
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
         =~ scheme (T.Scheme.create ~quantifiers:[ q1 ] (var q1))
         >> (var a1 =~ scheme (T.Scheme.create ~quantifiers:[ q2 ] (var q2 @-> var q2))))
  in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is unsatisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
          ((quantifiers (((id 1) (name Type.Var))))
           (body (Var ((id 1) (name Type.Var)))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
          ((quantifiers (((id 2) (name Type.Var))))
           (body
            (Arrow (Var ((id 2) (name Type.Var))) (Var ((id 2) (name Type.Var)))))))))))
     (err
      ((it
        (Cannot_unify
         (Scheme
          ((quantifiers (((id 0) (name Decoded_type.Var))))
           (body (Var ((id 0) (name Decoded_type.Var))))))
         (Scheme
          ((quantifiers (((id 1) (name Decoded_type.Var))))
           (body
            (Arrow (Var ((id 1) (name Decoded_type.Var)))
             (Var ((id 1) (name Decoded_type.Var)))))))))
       (range ()))))
    |}]
;;

let%expect_test "" =
  (* Nested type schemes. *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let q1 = T.Var.create ~id_source () in
  let q2 = T.Var.create ~id_source () in
  let q3 = T.Var.create ~id_source () in
  let q4 = T.Var.create ~id_source () in
  let scheme1 =
    T.Scheme.create
      ~quantifiers:[ q1 ]
      T.(
        tuple [ var q1; scheme (T.Scheme.create ~quantifiers:[ q2 ] (var q1 @-> var q2)) ])
  in
  let scheme2 =
    T.Scheme.create
      ~quantifiers:[ q3 ]
      T.(
        tuple [ var q3; scheme (T.Scheme.create ~quantifiers:[ q4 ] (var q3 @-> var q4)) ])
  in
  let cst = exists a1 @@ T.(var a1 =~ scheme scheme1 >> (var a1 =~ scheme scheme2)) in
  print_solve_result cst;
  [%expect
    {|
    ("Constraint is satisfiable"
     (cst
      (Exists ((id 0) (name Type.Var))
       (Conj
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
          ((quantifiers (((id 1) (name Type.Var))))
           (body
            (Tuple
             ((Var ((id 1) (name Type.Var)))
              (Scheme
               ((quantifiers (((id 2) (name Type.Var))))
                (body
                 (Arrow (Var ((id 1) (name Type.Var)))
                  (Var ((id 2) (name Type.Var)))))))))))))
        (Eq (Var ((id 0) (name Type.Var)))
         (Scheme
          ((quantifiers (((id 3) (name Type.Var))))
           (body
            (Tuple
             ((Var ((id 3) (name Type.Var)))
              (Scheme
               ((quantifiers (((id 4) (name Type.Var))))
                (body
                 (Arrow (Var ((id 3) (name Type.Var)))
                  (Var ((id 4) (name Type.Var)))))))))))))))))
    |}]
;;

let%expect_test "" =
  (* Monomorphism in type schemes. *)
  let open C in
  let id_source = Identifier.create_source () in
  let a1 = T.Var.create ~id_source () in
  let a2 = T.Var.create ~id_source () in
  let q1 = T.Var.create ~id_source () in
  let cst =
    exists_many [ a1; a2 ]
    @@ T.(
         var a1
         =~ scheme (T.Scheme.create ~quantifiers:[ q1 ] (tint @-> var q1))
         >> (var a1 =~ scheme (T.Scheme.create ~quantifiers:[ q1 ] (var a2 @-> var q1)))
         >> (var a2 =~ tstring))
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
           (Scheme
            ((quantifiers (((id 2) (name Type.Var))))
             (body
              (Arrow (Constr () ((id 0) (name int)))
               (Var ((id 2) (name Type.Var))))))))
          (Eq (Var ((id 0) (name Type.Var)))
           (Scheme
            ((quantifiers (((id 2) (name Type.Var))))
             (body
              (Arrow (Var ((id 1) (name Type.Var)))
               (Var ((id 2) (name Type.Var)))))))))
         (Eq (Var ((id 1) (name Type.Var))) (Constr () ((id 1) (name string))))))))
     (err
      ((it
        (Cannot_unify (Constr () ((id 0) (name int)))
         (Constr () ((id 1) (name string)))))
       (range ()))))
    |}]
;;
