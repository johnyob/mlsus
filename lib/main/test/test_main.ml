open! Core
open! Grace
open Mlsus_main

let () =
  Async.Log.Global.For_testing.use_test_output ();
  Mlsus_error.For_testing.use_expect_test_config ()
;;

let type_check_and_print
      ?(dump_ast = false)
      ?(dump_constraint = false)
      ?(with_stdlib = true)
      ?(log_level = `Info)
      str
  =
  Async.Log.Global.set_level log_level;
  let source = Mlsus_source.For_testing.expect_test_source str in
  type_check_and_print
    ~source
    ~dump_ast
    ~dump_constraint
    ~with_stdlib
    (Lexing.from_string ~with_positions:true str)
;;

let include_ref =
  {|
    type 'a ref;;
    type 'a ref_repr = { contents : 'a };;

    external create_ref : 'a. 'a -> 'a ref;;
    external get_ref : 'a. 'a ref -> 'a;;
    external set_ref : 'a. 'a ref -> 'a -> unit;;
    external ref_repr : 'a. 'a ref -> 'a ref_repr;;
  |}
;;

let include_fix = "external fix : 'a 'b. (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b;;"

let include_list =
  {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    ;;

    external map_list : 'a 'b. ('a -> 'b) -> 'a list -> 'b list;;
  |}
;;

let include_array =
  {|
    type 'a array;; 

    external map_array : 'a 'b. ('a -> 'b) -> 'a array -> 'b array;;
  |}
;;

let include_option =
  {|
    type 'a option = 
      | None 
      | Some of 'a 
    ;;
  |}
;;

let%expect_test "" =
  let str =
    include_fix
    ^ {|
      let power = fix (fun power x n -> 
          if n = 0 
            then 1
            else x * power x (n - 1) 
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ {|
      external mod : int -> int -> int;;

      let even = fun n -> mod n 2 = 0;;

      let power = fix (fun power x n ->
          if n = 1 
            then x
            else if even n 
              then power (x * x)  (n / 2)
              else x * power (x * x) (n / 2)
        )
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ {|
      let sum = 
        fix (fun sum n -> 
          if n = 0 then 0 
          else n + sum (n - 1))
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ {|
      let sum = fun n ->
        let loop = fix (fun loop n acc ->
          if n = 0 then acc
          else loop (n - 1) (n + acc))
        in loop n
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      let mem = fix (fun mem t x equal ->
        match t with
        ( Nil -> false
        | Cons (y, t) -> 
          if equal x y then true 
          else mem t x equal 
        ))
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      let zip = 
        fix (fun zip t1 t2 ->
          match (t1, t2) with
          ( (Cons (x1, t1), Cons (x2, t2)) ->
              Cons ((x1, x2), zip t1 t2) 
          | _ -> Nil  
          ))
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      let unzip = 
        fix (fun unzip t ->
          match t with
          ( Nil -> (Nil, Nil)
          | Cons ((x1, x2), t) ->
            let t1t2 = unzip t in
            match t1t2 with (
              (t1, t2) -> (Cons (x1, t1), Cons (x2, t2))
            )   
          )
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      external raise_no_more_coins : 'a. unit -> 'a;; 
      
      let change = 
        fix (fun change till amt ->
          match (till, amt) with
          ( (_, 0) -> Nil
          | (Nil, _) -> raise_no_more_coins ()
          | (Cons (c, till), amt) ->
            if amt < c then change till amt
            else Cons (c, change (Cons (c, till)) (amt - c) )     
          )
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      external append : 'a. 'a list -> 'a list -> 'a list;;

      let change = 
        fix (fun change till amt ->
          match (till, amt) with
          ( (_, 0) -> Cons (Nil, Nil)
          | (Nil, _) -> Nil
          | (Cons (c, till), amt) ->
            if amt < c then change till amt
            else 
              let loop = fix (fun loop t -> 
                  match t with
                  ( Nil -> Nil
                  | Cons (cs, css) -> Cons (Cons (c, cs), loop css)
                  )
                )
              in
                append 
                  (loop (change (Cons (c, till)) (amt - c)))
                  (change till amt)  
          )
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      let change = 
        fix (fun change till amt ->
          let loop = fix 
            (fun loop till amt chg chgs ->
              match (till, amt) with
              ( (_, 0) -> Cons (chg, chgs)
              | (Nil, _) -> chgs
              | (Cons (c, till), amt) ->
                  if amt < 0 then chgs
                  else
                    loop (Cons (c, till)) (amt - c) (Cons (c, chg)) (loop till amt chg chgs) 
              )
            )
          in loop till amt Nil Nil
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      type vehicle = 
        | Bike
        | Motorbike
        | Car
        | Lorry
      ;;

      let m = Motorbike;;

      let wheels = 
        fun t -> 
          match t with
          ( Bike -> 2
          | Motorbike -> 2
          | Car -> 4
          | Lorry -> 18
          )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      type vehicle = 
        | Bike
        | Motorbike of int (* engine size in CCs *)
        | Car of bool (* true if a Reliant Robin *)
        | Lorry of int (* number of wheels *)
      ;;

      let wheels = 
        fun t ->
          match t with
          ( Bike -> 2
          | Motorbike _ -> 2
          | Car is_robin -> if is_robin then 3 else 4
          | Lorry w -> w
          )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_option
    ^ {|
      let x = Some 1;;

      let y = None;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      external raise_no_change : 'a. int -> 'a;; 
      external try_with_no_change : 'a. (unit -> 'a) -> (int -> 'a) -> 'a;;

      let change = 
        fix (fun change till amt ->
          match (till, amt) with
          ( (_, 0) -> Nil
          | (Nil, amt) -> raise_no_change amt
          | (Cons (c, till), amt) ->
              if amt < c 
                then raise_no_change amt
                else try_with_no_change 
                      (fun () -> Cons (c, change (Cons (c, till)) (amt - c)))
                      (fun _ -> change till amt)
          )
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      type shape = 
        | Null
        | Circle of int (* radius *)
        | Join of shape * shape
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      type 'a tree = 
        | Lf
        | Br of 'a tree * 'a * 'a tree
      ;;

      external append : 'a. 'a list -> 'a list -> 'a list;;

      let pre_order = 
        fix (fun pre_order t ->
          match t with
          ( Lf -> Nil
          | Br (l, x, r) ->
            append (Cons (x, Nil)) 
              (append (pre_order l) (pre_order r))
          )
        )
      ;;

      let in_order = 
        fix (fun in_order t ->
          match t with
          ( Lf -> Nil
          | Br (l, x, r) ->
            append (pre_order l)
              (append (Cons (x, Nil)) (pre_order r))
          )
        )
      ;;

      let post_order = 
        fix (fun post_order t ->
          match t with
          ( Lf -> Nil
          | Br (l, x, r) ->
            append (post_order l)
              ( append (post_order r) (Cons (x, Nil)) )  
          )
        )
      ;;

      let in_order = fun t ->
        let loop = 
          fix (fun loop t acc ->
            match t with
            ( Lf -> acc
            | Br (l, x, r) -> 
              loop l (Cons (x, loop r acc))
            )
          )
        in loop t
      ;;

      let pre_order = fun t ->
        let loop = 
          fix (fun loop t acc ->
            match t with
            ( Lf -> acc
            | Br (l, x, r) ->
              Cons (x, loop l (loop r acc))
            )
          )
        in loop t
      ;;

      let post_order = fun t ->
        let loop = 
          fix (fun loop t acc ->
            match t with
            ( Lf -> acc
            | Br (l, x, r) ->
              loop l (loop r (Cons (x, acc)))  
            )
          )
        in loop t
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_list
    ^ {|
      let a1 = 
        Cons (fun n -> n * 2, Cons (fun n -> n * 3, Cons (fun n -> n + 1, Nil)))
      ;;

      let a2 = 
        fun n -> n * 2
      ;;

      let a3 = 
        (fun n -> n * 2) 17
      ;;

      let double = fun n -> n * 2;;

      let a4 = 
        fun x -> match x with (0 -> true | _ -> false)
      ;;

      let is_zero = 
        fun x -> match x with (0 -> true | _ -> false)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      external map : 'a 'b. ('a -> 'b) -> 'a list -> 'b list;;
      external hd : 'a. 'a list -> 'a;;
      external tl : 'a. 'a list -> 'a list;;

      let transpose = 
        fix (fun transpose t ->
          match t with
          ( Cons (Nil, _) -> Nil
          | rows ->
            Cons (map hd rows, transpose (map tl rows))
          )
        )
      ;;

      let dot_product = 
        fix (fun dot_product xs ys ->
          match (xs, ys) with
          ( (Nil, Nil) -> 0
          | (Cons (x, xs), Cons (y, ys)) ->
              (x * y) + dot_product xs ys
          )
        )
      ;;


      let product = 
        fun a b ->
          let c = transpose b in
          map (fun rows -> map (dot_product rows) c) a
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ {|
      type 'a tree = 
        | Lf
        | Br of 'a tree * 'a * 'a tree
      ;;

      let cons = 
        fix (fun cons t x ->
          match t with
          ( Lf -> Br (Lf, x, Lf)
          | Br (l, y, r) ->
              Br (cons l y, x, r)  
          )
        )
      ;;
      
      external invalid_arg : 'a. unit -> 'a;;

      let uncons =
        fix (fun uncons t -> 
          match t with
          ( Lf -> invalid_arg ()
          | Br (Lf, x, Lf) -> (x, Lf)
          | Br (l, x, r) ->
            match uncons l with (
              (y, l') -> (x, Br (r, x, l'))
            )
          )
        )
      ;;

      let hd = fun t ->
        match uncons t with ((x, _) -> x)
      ;;

      let tl = fun t ->
        match uncons t with ((_, t) -> t)
      ;;

      external mod : int -> int -> int;;

      let even = fun n -> mod n 2 = 0;;

      let nth = 
        fix (fun nth t n ->
          match (t, n) with
          ( (Lf, _) -> invalid_arg ()
          | (Br (_, x, _), 0) -> x
          | (Br (l, x, r), n) ->
              if even n then nth r (n / 2)
              else nth l (n / 2)
          )
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      type 'a tree = 
        | Lf
        | Br of 'a tree * 'a * 'a tree
      ;;

      external raise_empty : 'a. unit -> 'a;;

      type 'a queue = Q of 'a list * 'a list;;
      let empty = Q (Nil, Nil);;

      let is_empty = fun q ->
        match q with
        ( Q (Nil, Nil) -> true
        | _ -> false)
      ;;

      external rev : 'a. 'a list -> 'a list;;

      let norm = fun q ->
        match q with
        ( Q (Nil, ys) -> Q (rev ys, Nil)
        | q -> q
        )
      ;;

      let enqueue = fun (Q (xs, ys)) y -> norm (Q (xs, Cons (y, ys)));;
      let dequeue = fun q ->
        match q with
        ( Q (Cons (x, xs), ys) -> norm (Q (xs, ys))
        | _ -> raise_empty ()
        )
      ;;

      let hd = fun q ->
        match q with
        ( Q (Cons (x, _), _) -> x
        | _ -> raise_empty ()
        )
      ;;

      let bfs = 
        fix (fun bfs q -> 
          if is_empty q then Nil
          else
            match hd q with
            ( Lf -> bfs (dequeue q)
            | Br (l, x, r) ->
              Cons (x, bfs (enqueue (enqueue (dequeue q) l) r) ) 
            )
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_fix
    ^ include_list
    ^ {|
      type 'a seq = 
        | Seq_nil
        | Seq_cons of 'a * (unit -> 'a seq)
      ;;

      external raise_empty : 'a. unit -> 'a;;

      let hd = fun t ->
        match t with
        ( Seq_cons (x, _) -> x
        | _ -> raise_empty ()
        )
      ;;

      let tl = fun t ->
        match t with
        ( Seq_cons (_, tf) -> tf ()
        | _ -> raise_empty ()
        )
      ;;

      let empty = Seq_nil ;;

      let is_empty = fun t ->
        match t with
        ( Seq_nil -> true
        | _ -> false
        )
      ;;

      let map = 
        fix (fun map f t ->
          match t with
          ( Seq_nil -> Seq_nil
          | Seq_cons (x, tf) -> Seq_cons (f x, fun () -> map f (tf ()))
          ) 
        )
      ;;

      let filter = 
        fix (fun filter f t ->
          match t with
          ( Seq_nil -> Seq_nil
          | Seq_cons (x, tf) ->
              if f x then
                Seq_cons (x, fun () -> filter f (tf ()))
              else
                filter f (tf ())   
          )
        )
      ;;

      let append = 
        fix (fun append t1 t2 ->
          match t1 with
          ( Seq_nil -> t2
          | Seq_cons (x, t1f) ->
              Seq_cons (x, fun () -> append (t1f ()) t2)  
          ) 
        )
      ;;

      let interleave = 
        fix (fun interleave t1 t2 ->
          match t1 with
          ( Seq_nil -> t2
          | Seq_cons (x, t1f) ->
              Seq_cons (x, fun () -> interleave t2 (t1f ()))  
          )
        )
      ;;

      let binary_string = 
        fix (fun binary_string bits ->
          Seq_cons (bits, fun () -> 
            interleave
              (binary_string (Cons (0, bits)))
              (binary_string (Cons (1, bits))))
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> y ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E004]: cannot find value `y` in this scope
        ┌─ expect_test.ml:2:25
      2 │        let id = fun x -> y ;;
        │                          ^ not found in this scope
    |}]
;;

let%expect_test "" =
  let str =
    {|
      (* val id : ('a -> 'a as 'a) -> 'a -> 'a *)
      let id = exists (type 'a) ->
        (fun x -> x : 'a -> 'a -> 'a)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let app_error = fun x ->
        (x, x) (fun y -> y)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:9
      3 │          (x, x) (fun y -> y)
        │          ^^^^^^ `'a -> 'b` is not equal to `'c * 'd`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let x =
        (fun y z -> y z) ()
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:26
      3 │          (fun y z -> y z) ()
        │                           ^^ `'a -> 'b` is not equal to `unit`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type t = 
        | A
      ;; 

      type u = 
        | A
      ;; 

      let x = (A : t) ;;
      let y = (A : u) ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      type t = 
        | A
      ;; 

      type u = 
        | A
      ;; 

      let z = A ;;
  |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|    
      type r = 
        | K of int 
      ;; 

      type s = 
        | K of int 
      ;; 

      let a = 
        fun old ->
          let g = fun x -> 1 + old (K x) in
          (g 0, (old : r -> int))
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|    
      type m = 
        | L 
      ;; 

      type n = 
        | L 
      ;; 

      let x1 = (fun (z : m) -> 1) L ;; 

      let y1 = fun z -> (z : m -> int) L ;;

      let z1 = (fun z -> match z with (L -> 1)) (L : m) ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      type m = 
        | L 
      ;;

      type n = 
        | L 
      ;; 

      let bad = 
        let f = fun x -> match x with (L -> 1) in 
        f (L : m)
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:12:11
     12 │          f (L : m)
        │            ^^^^^^^ `n` is not equal to `m`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;; 
    |}
  in
  (* Show that stdlib is not added to generated constraint *)
  type_check_and_print ~with_stdlib:false ~dump_constraint:true str;
  [%expect
    {|
    Generated constraint:
    (With_range
     (Let ((id 4) (name id))
      ((type_vars ((Flexible ((id 0) (name Type.Var)))))
       (in_
        (With_range
         (Exists ((id 1) (name Type.Var))
          (Exists ((id 2) (name Type.Var))
           (Conj
            (Eq (Var ((id 0) (name Type.Var)))
             (Arrow (Var ((id 1) (name Type.Var)))
              (Var ((id 2) (name Type.Var)))))
            (With_range
             (Conj True
              (Let ((id 3) (name x))
               ((type_vars ()) (in_ True) (type_ (Var ((id 1) (name Type.Var)))))
               (With_range
                (Instance ((id 3) (name x)) (Var ((id 2) (name Type.Var))))
                ((start 25) (stop 26)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 35)
                    (unsafe_get <fun>))))))))
             ((start 20) (stop 21)
              (source
               (Reader
                ((id 0) (name (expect_test.ml)) (length 35) (unsafe_get <fun>)))))))))
         ((start 16) (stop 26)
          (source
           (Reader
            ((id 0) (name (expect_test.ml)) (length 35) (unsafe_get <fun>)))))))
       (type_ (Var ((id 0) (name Type.Var)))))
      True)
     ((start 7) (stop 26)
      (source
       (Reader ((id 0) (name (expect_test.ml)) (length 35) (unsafe_get <fun>))))))
    Well typed :)
    |}]
;;

let include_mr_ms_records =
  {|
    type mr = { lbl : int };; 
    type ms = { lbl : bool };;
  |}
;;

let%expect_test "" =
  let str =
    {|
      let magic = 
        forall (type 'a 'b) -> 
          (fun x -> x : 'a -> 'b)
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:4:21
      4 │            (fun x -> x : 'a -> 'b)
        │                      ^ `'a` is not equal to `'b`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let escape = fun f -> 
        forall (type 'a) -> 
          (f : 'a -> 'a)
      ;; 
    |}
    |> Dedent.string
  in
  type_check_and_print str;
  (* NOTE():
     error message looks off due to bug in Grace[^1]

     [1]: https://github.com/johnyob/grace/issues/42 *)
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:2:3
      1 │    let escape = fun f ->
      2 │ ╭    forall (type 'a) ->
      3 │ │      (f : 'a -> 'a)
        │ ╰──
      4 │    ;;
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let escape = fun x ->
        forall (type 'a) -> 
          (x : 'a)
      ;;
    |}
    |> Dedent.string
  in
  type_check_and_print str;
  (* NOTE():
     error message looks off due to bug in Grace[^1]

     [1]: https://github.com/johnyob/grace/issues/42 *)
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:2:3
      1 │    let escape = fun x ->
      2 │ ╭    forall (type 'a) ->
      3 │ │      (x : 'a)
        │ ╰──
      4 │    ;;
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let x = 
        (forall (type 'a) -> fun (x : 'a) -> (x : 'a)) ()
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ {|
      let before_a = ({ lbl = 3 } : mr);; 
      
      let a = 
        let x = ({ lbl = 3 } : mr) in 
        x.lbl 
      ;; 

      let after_a = 
        let x = ({ lbl = 3 } : mr) in
        ({ lbl = x.lbl } : mr)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    {|
      let x = 
        (forall (type 'a) -> ((fun x -> fun y -> y) (fun x -> x) : 'a -> 'a))
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ include_ref
    ^ {|
      let b = 
        let x = (create_ref { lbl = 3 } : mr ref) in 
        set_ref x { lbl = 4 }
      ;; 

      let c = 
        let x = (create_ref { lbl = 3 } : mr ref) in 
        (get_ref x).lbl
      ;; 

      let f = 
        let x = (create_ref { lbl = 3 } : mr ref) in
        (ref_repr x).contents.lbl
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ include_ref
    ^ {|
      let g = fun (x : mr) -> 
        match x with ( { lbl = 1 } -> () )
      ;; 

      let h = fun x -> 
        match x with (
        | (_ : mr) -> () 
        | { lbl = 1 } -> ()
        )
      ;; 

      let i = fun x ->
        match x with (
        | { lbl = 1 } -> () 
        | (_ : mr) -> ()
        )
      ;;

      let l = fun (x : mr ref) -> 
        match (ref_repr x) with 
        ( { contents = { lbl = 1 } } -> () )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ include_ref
    ^ {|
      let m = fun x -> 
        match x with 
        ( { contents = { lbl = _ } } -> () )
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ include_ref
    ^ {|
      let n = fun x -> 
        match x with 
        ( (_ : mr ref_repr) -> ()
        | { contents = { lbl = _ } } -> () 
        )
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ include_ref
    ^ {|
      let o = fun x -> 
        match x with 
        ( (_ : mr ref_repr) -> ()
        | { contents = { lbl = _ } } -> () 
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_records
    ^ include_ref
    ^ {|
      let r = fun arg -> 
        match arg with ( (x : mr ref) -> (get_ref x).lbl )
      ;; 

      let s = fun arg -> 
        match arg with ( 
          (x : mr ref) -> set_ref x { lbl = 4 }
        )
      ;; 

      let t = fun arg -> 
        match (ref_repr arg) with 
        ( ({ contents = { lbl = _ } } : mr ref_repr) -> 
            set_ref arg { lbl = 4 } 
        )
      ;;

      let u = fun arg -> 
        match (ref_repr arg) with 
        ( ({ contents = { lbl = _ } } : mr ref_repr) -> 
            (get_ref arg).lbl
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let include_mr_ms_constrs =
  {|
    type mr = 
      | A 
      | B 
    ;; 

    type ms = 
      | A 
      | B 
    ;;
  |}
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let before_a = (A : mr);; 
      
      let a = 
        let x = (A : mr) in 
        x
      ;; 

      let b = 
        let x = (create_ref A : mr ref) in
        set_ref x B
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let g = fun (x : mr) -> 
        match x with 
        ( A -> () 
        | B -> ()
        )
      ;;

      let h = fun x -> 
        match x with 
        ( (A : mr) -> () 
        | B -> ()
        )
      ;;

      let i = fun x -> 
        match x with 
        ( A -> () 
        | (B : mr) -> ()
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let l = fun (x : mr ref) -> 
        match (ref_repr x) with 
        ( { contents = A } -> () 
        | { contents = B } -> ()
        )
      ;;
  |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let m = fun x -> 
        match (ref_repr x) with 
        ( { contents = A } -> () 
        | { contents = B } -> ()
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let n = fun x -> 
        match (ref_repr x) with 
        ( (_ : mr ref_repr) -> () 
        | { contents = A } -> ()
        )
      ;;

      let o = fun x -> 
        match (ref_repr x) with 
        ( (_ : mr ref_repr) -> () 
        | { contents = A } -> ()
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let s = fun arg -> 
        match arg with 
        ( (_ : mr ref) -> set_ref arg A )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_mr_ms_constrs
    ^ include_ref
    ^ {|
      let t = fun arg -> 
        match (ref_repr arg) with 
        ( ({ contents = A } : mr ref_repr) -> 
            set_ref arg B
        )
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let include_float =
  {|
    type float;; 

    external add_float : float -> float -> float;;
    external sub_float : float -> float -> float;;
    external div_float : float -> float -> float;;
    external mul_float : float -> float -> float;;

    external compare_float : float -> float -> int;;

    external float_of_int : int -> float;;

    let zero_float = float_of_int 0;;
    let neg_float = fun n -> sub_float zero_float n;;
  |}
;;

let include_string =
  {|
    type string;;

    external empty_string : string;;
    external concat_string : string -> string -> string;;
    external length_string : string -> int;;
  |}
;;

let%expect_test "" =
  let str =
    include_string
    ^ {|
      let x = 1;; 
      let y = true;; 
      let z = empty_string;;

      let f = 
        let a = x in 
        let over a = y in 
        let over a = z in 
        (a : int)
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_float
    ^ include_array
    ^ include_list
    ^ {|
      let add = fun x y -> x + y;; 
      let over add = add_float;; 

      let mul = fun x y -> x * y;;
      let over mul = mul_float;;

      let compare = fun x y -> 
        if x < y then -1
        else if x > y then 1
        else 0
      ;; 
      let over compare = compare_float;;

      let zero = 0;; 
      let over zero = zero_float;; 

      let one = 1;; 
      let over one = float_of_int one;;

      let two = 2;;
      let over two = float_of_int two;;  

      let three = 3;;
      let over three = float_of_int three;;

      let four = 4;;
      let over four = float_of_int four;;

      let fourty_two = 42;;
      let over fourty_two = float_of_int fourty_two;;

      let ex1 = fun (x : int) (y : int) -> add x y;;
      let ex2 = fun (x : float) (y : float) -> add x y;;

      let ex3 = (zero : int);; 

      let ex4 = fun (x : int) -> add x zero;; 
      let ex5 = fun (x : float) -> add x zero;;
      
      let ex6 = 
        (add (add three four) (add one (add zero two)) : float)
      ;; 

      let ex7 = 
        (add (add three four) (add one (add zero two)) : int)
      ;; 

      let ex8 = fun (x : float) ->
        if (compare x zero < 0) then 
          add zero one 
        else 
          mul two x 
      ;;
      
      let exlet1 = fun (f : int -> int) (g : int -> int) (x : int) -> 
        (add (f (add x fourty_two)) (g (add (mul two x) fourty_two)) : int)
      ;; 

      let exlet1' = fun (f : float -> float) (g : float -> float) x -> 
        add (f (add x fourty_two)) (g (add (mul two x) fourty_two))
      ;;

      let exlet1'' = fun (f : float -> float) g x -> 
        add (f (add x fourty_two)) (g (add (mul two x) fourty_two))
      ;;

      let exlet2 = fun (f : int -> int) (g : int -> int) (x : int) -> 
        (* annotation required since application sites do not influence types 
           of generics. *)
        let op = fun (n : int) -> add n fourty_two in 
        (add (f (op x)) (g (op (mul two x))) : int)
      ;; 

      let exlet2' = fun (f : float -> float) (g : float -> float) x -> 
        let op = fun (n : float) -> add n fourty_two in 
        add (f (op x)) (g (op (mul two x)))
      ;; 

      let map = map_list;;
      let over map = map_array;;

      external d : float array;; 

      let ex12 = 
        map (fun x -> add (mul two x) one) d
      ;; 

      let example_success =
        let x = (zero : float) in 
        let y = add one x in 
        let z = (two : float) in 
        let t = (add (add three y) (add four z) : float) in 
        add (add four z) one 
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;

let%expect_test "" =
  let str =
    include_string
    ^ {|
      let add = fun x y -> x + y;; 
      let concat = (concat_string : string -> string -> string);; 

      let g0 = fun x -> 
        let f = add in 
        let over f = concat in
        f 1 x 
      ;;

      let g1 = fun (x : int) -> 
        let f = add in 
        let over f = concat in
        let fx = f x in 
        let a = 1 in 
        let over a = empty_string in 
        let z = (f : int -> int -> int) a in 
        (fx, z)
      ;; 
    |}
  in
  type_check_and_print str;
  [%expect {| Well typed :) |}]
;;
