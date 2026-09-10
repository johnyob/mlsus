open! Core
open! Grace
open! Omniml_log

let () = Global.For_testing.use_test_output ()

let type_check_and_print
      ?(dump_ast = false)
      ?(dump_constraint = false)
      ?(with_stdlib = true)
      ?(with_fcp = false)
      ?(rec_types = true)
      ?defaulting
      ?(log_level = `Info)
      str
  =
  Omniml_error.handle_uncaught ~use_ansi:false ~exit:false
  @@ fun () ->
  Global.set_level log_level;
  let source = Omniml_source.For_testing.expect_test_source str in
  let options =
    let defaulting = Option.value defaulting ~default:with_fcp in
    Omniml_options.(
      empty
      |> with_ ~option:Dump_ast ~enabled:dump_ast
      |> with_ ~option:Dump_constraint ~enabled:dump_constraint
      |> with_ ~option:Include_stdlib ~enabled:with_stdlib
      |> with_ ~option:First_class_polymorphism ~enabled:with_fcp
      |> with_ ~option:Recursive_types ~enabled:rec_types
      |> with_ ~option:Defaulting ~enabled:defaulting)
  in
  Omniml_main.type_check_and_print
    ~source
    ~options
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    val power : int -> int -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    val power : int -> int -> int
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    external mod : int -> int -> int
    val even : int -> bool
    val power : int -> int -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    external mod : int -> int -> int
    val even : int -> bool
    val power : int -> int -> int
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    val sum : int -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    val sum : int -> int
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    val sum : int -> int -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    val sum : int -> int -> int
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val mem : 'c list -> 'd -> ('d -> 'c -> bool) -> bool
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val mem : 'c list -> 'd -> ('d -> 'c -> bool) -> bool
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val zip : 'c list -> 'd list -> ('c * 'd) list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val zip : 'c list -> 'd list -> ('c * 'd) list
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val unzip : ('c * 'd) list -> 'c list * 'd list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val unzip : ('e * 'f) list -> 'e list * 'f list
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external raise_no_more_coins : unit -> 'c
    val change : int list -> int -> int list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external raise_no_more_coins : unit -> 'c
    val change : int list -> int -> int list
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external append : 'c list -> 'c list -> 'c list
    val change : int list -> int -> int list list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external append : 'c list -> 'c list -> 'c list
    val change : int list -> int -> int list list
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val change : int list -> int -> int list list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val change : int list -> int -> int list list
    |}]
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
  [%expect
    {|
    type vehicle =
      | Bike
      | Motorbike
      | Car
      | Lorry
    val m : vehicle
    val wheels : vehicle -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type vehicle =
      | Bike
      | Motorbike
      | Car
      | Lorry
    val m : vehicle
    val wheels : vehicle -> int
    |}]
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
  [%expect
    {|
    type vehicle =
      | Bike
      | Motorbike of int
      | Car of bool
      | Lorry of int
    val wheels : vehicle -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type vehicle =
      | Bike
      | Motorbike of int
      | Car of bool
      | Lorry of int
    val wheels : vehicle -> int
    |}]
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
  [%expect
    {|
    type 'a option =
      | None
      | Some of 'a
    val x : int option
    val y : 'a option
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type 'a option =
      | None
      | Some of 'a
    val x : int option
    val y : 'a option
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external raise_no_change : int -> 'c
    external try_with_no_change : (unit -> 'd) -> (int -> 'd) -> 'd
    val change : int list -> int -> int list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external raise_no_change : int -> 'c
    external try_with_no_change : (unit -> 'd) -> (int -> 'd) -> 'd
    val change : int list -> int -> int list
    |}]
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
  [%expect
    {|
    type shape =
      | Null
      | Circle of int
      | Join of shape * shape
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type shape =
      | Null
      | Circle of int
      | Join of shape * shape
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    type 'a tree =
      | Lf
      | Br of 'a tree * 'a * 'a tree
    external append : 'c list -> 'c list -> 'c list
    val pre_order : 'd tree -> 'd list
    val in_order : 'e tree -> 'e list
    val post_order : 'f tree -> 'f list
    val in_order : 'h tree -> 'h list -> 'h list
    val pre_order : 'j tree -> 'j list -> 'j list
    val post_order : 'l tree -> 'l list -> 'l list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    type 'a tree =
      | Lf
      | Br of 'a tree * 'a * 'a tree
    external append : 'c list -> 'c list -> 'c list
    val pre_order : 'd tree -> 'd list
    val in_order : 'e tree -> 'e list
    val post_order : 'f tree -> 'f list
    val in_order : 'h tree -> 'h list -> 'h list
    val pre_order : 'j tree -> 'j list -> 'j list
    val post_order : 'l tree -> 'l list -> 'l list
    |}]
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
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val a1 : (int -> int) list
    val a2 : int -> int
    val a3 : int
    val double : int -> int
    val a4 : int -> bool
    val is_zero : int -> bool
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val a1 : (int -> int) list
    val a2 : int -> int
    val a3 : int
    val double : int -> int
    val a4 : int -> bool
    val is_zero : int -> bool
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external map : ('c -> 'd) -> 'c list -> 'd list
    external hd : 'e list -> 'e
    external tl : 'f list -> 'f list
    val transpose : 'g list list -> 'g list list
    val dot_product : int list -> int list -> int
    val product : int list list -> int list list -> int list list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external map : ('c -> 'd) -> 'c list -> 'd list
    external hd : 'e list -> 'e
    external tl : 'f list -> 'f list
    val transpose : 'g list list -> 'g list list
    val dot_product : int list -> int list -> int
    val product : int list list -> int list list -> int list list
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a tree =
      | Lf
      | Br of 'a tree * 'a * 'a tree
    val cons : 'c tree -> 'c -> 'c tree
    external invalid_arg : unit -> 'd
    val uncons : 'e tree -> 'e * 'e tree
    val hd : 'f tree -> 'f
    val tl : 'g tree -> 'g tree
    external mod : int -> int -> int
    val even : int -> bool
    val nth : 'h tree -> int -> 'h
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a tree =
      | Lf
      | Br of 'a tree * 'a * 'a tree
    val cons : 'c tree -> 'c -> 'c tree
    external invalid_arg : unit -> 'd
    val uncons : 'e tree -> 'e * 'e tree
    val hd : 'f tree -> 'f
    val tl : 'g tree -> 'g tree
    external mod : int -> int -> int
    val even : int -> bool
    val nth : 'h tree -> int -> 'h
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    type 'a tree =
      | Lf
      | Br of 'a tree * 'a * 'a tree
    external raise_empty : unit -> 'c
    type 'a queue =
      | Q of 'a list * 'a list
    val empty : 'd queue
    val is_empty : 'e queue -> bool
    external rev : 'f list -> 'f list
    val norm : 'g queue -> 'g queue
    val enqueue : 'h queue -> 'h -> 'h queue
    val dequeue : 'i queue -> 'i queue
    val hd : 'j queue -> 'j
    val bfs : 'k tree queue -> 'k list
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    type 'a tree =
      | Lf
      | Br of 'a tree * 'a * 'a tree
    external raise_empty : unit -> 'c
    type 'a queue =
      | Q of 'a list * 'a list
    val empty : 'd queue
    val is_empty : 'e queue -> bool
    external rev : 'f list -> 'f list
    val norm : 'g queue -> 'g queue
    val enqueue : 'h queue -> 'h -> 'h queue
    val dequeue : 'i queue -> 'i queue
    val hd : 'j queue -> 'j
    val bfs : 'k tree queue -> 'k list
    |}]
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
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    type 'a seq =
      | Seq_nil
      | Seq_cons of 'a * (unit -> 'a seq)
    external raise_empty : unit -> 'c
    val hd : 'd seq -> 'd
    val tl : 'e seq -> 'e seq
    val empty : 'f seq
    val is_empty : 'g seq -> bool
    val map : ('h -> 'i) -> 'h seq -> 'i seq
    val filter : ('j -> bool) -> 'j seq -> 'j seq
    val append : 'k seq -> 'k seq -> 'k seq
    val interleave : 'l seq -> 'l seq -> 'l seq
    val binary_string : int list -> int list seq
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    type 'a seq =
      | Seq_nil
      | Seq_cons of 'a * (unit -> 'a seq)
    external raise_empty : unit -> 'c
    val hd : 'd seq -> 'd
    val tl : 'e seq -> 'e seq
    val empty : 'f seq
    val is_empty : 'g seq -> bool
    val map : ('h -> 'i) -> 'h seq -> 'i seq
    val filter : ('j -> bool) -> 'j seq -> 'j seq
    val append : 'k seq -> 'k seq -> 'k seq
    val interleave : 'l seq -> 'l seq -> 'l seq
    val binary_string : int list -> int list seq
    |}]
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
    |}];
  type_check_and_print ~with_fcp:true str;
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
  [%expect {| val id : ('a -> 'a as 'a) -> ('b -> 'b as 'b) |}];
  type_check_and_print ~with_fcp:true str;
  [%expect {| val id : ('a -> 'a as 'a) -> ('b -> 'b as 'b) -> ('c -> 'c as 'c) |}]
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
        │          ^^^^^^ `'a * 'a`
        │                   is not equal to
        │                 `'b -> 'c`
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:9
      3 │          (x, x) (fun y -> y)
        │          ^^^^^^ `'a * 'b`
        │                   is not equal to
        │                 `'c -> 'd`
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
        │                           ^^ `'a -> 'b`
        │                                is not equal to
        │                              `unit`
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:10
      3 │          (fun y z -> y z) ()
        │           ^^^^^^^^^^^^^^ `unit`
        │                            is not equal to
        │                          `'a -> 'b`
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
  [%expect
    {|
    type t =
      | A
    type u =
      | A
    val x : t
    val y : u
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type t =
      | A
    type u =
      | A
    val x : t
    val y : u
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

      let z = A ;;
  |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:10:15
     10 │        let z = A ;;
        │                ^
        = hint: add a type annotation
    |}];
  type_check_and_print ~defaulting:true str;
  [%expect
    {|
    type t =
      | A
    type u =
      | A
    val z : u
    |}]
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
  [%expect
    {|
    type r =
      | K of int
    type s =
      | K of int
    val a : (r -> int) -> int * (r -> int)
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type r =
      | K of int
    type s =
      | K of int
    val a : (r -> int) -> int * (r -> int)
    |}]
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
  [%expect
    {|
    type m =
      | L
    type n =
      | L
    val x1 : int
    val y1 : (m -> int) -> int
    val z1 : int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type m =
      | L
    type n =
      | L
    val x1 : int
    val y1 : (m -> int) -> int
    val z1 : int
    |}]
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

      let good =
        let f = fun x -> match x with (L -> 1) in
        f (L : m)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type m =
      | L
    type n =
      | L
    val good : int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type m =
      | L
    type n =
      | L
    val good : int
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
     (Let
      ((type_vars ((Flexible ((id 0) (name Type.Var)))))
       (in_
        (Conj
         (Conj
          (With_range
           (Exists ((id 1) (name Type.Var))
            (Exists ((id 2) (name Type.Var))
             (Conj
              (Conj
               (Eq (Var ((id 0) (name Type.Var)))
                (Arrow (Var ((id 1) (name Type.Var)))
                 (Var ((id 2) (name Type.Var)))))
               True)
              (Conj
               (With_range True
                ((start 20) (stop 21)
                 (source
                  (Reader
                   ((id 0) (name (expect_test.ml)) (length 34)
                    (unsafe_get <fun>))))))
               (Let
                ((type_vars ()) (in_ True)
                 (bindings
                  (((binding_var ((id 3) (name x)))
                    (binding_type (Var ((id 1) (name Type.Var))))))))
                (With_range
                 (Instance ((id 3) (name x)) (Var ((id 2) (name Type.Var))))
                 ((start 25) (stop 26)
                  (source
                   (Reader
                    ((id 0) (name (expect_test.ml)) (length 34)
                     (unsafe_get <fun>)))))))))))
           ((start 16) (stop 26)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>))))))
          (With_range True
           ((start 11) (stop 13)
            (source
             (Reader
              ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>)))))))
         (Conj (Decode (Var ((id 0) (name Type.Var)))) Return)))
       (bindings
        (((binding_var ((id 4) (name id)))
          (binding_type (Var ((id 0) (name Type.Var))))))))
      Return)
     ((start 7) (stop 26)
      (source
       (Reader ((id 0) (name (expect_test.ml)) (length 34) (unsafe_get <fun>))))))
    val id : 'a -> 'a
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect {| val id : 'a -> 'a |}]
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
        │                      ^ `'a`
        │                          is not equal to
        │                        `'b`
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:4:21
      4 │            (fun x -> x : 'a -> 'b)
        │                      ^ `'a`
        │                          is not equal to
        │                        `'b`
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
  (* Buggy with polyparams *)
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:2:3
      1 │    let escape = fun f ->
      2 │ ╭    forall (type 'a) ->
      3 │ │      (f : 'a -> 'a)
        │ ╰───────────────────^
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
  (* Buggy with polyparams *)
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:2:3
      1 │    let escape = fun x ->
      2 │ ╭    forall (type 'a) ->
      3 │ │      (x : 'a)
        │ ╰─────────────^
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
  [%expect {| val x : unit |}];
  type_check_and_print ~with_fcp:true str;
  [%expect {| val x : unit |}]
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
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    val before_a : mr
    val a : int
    val after_a : mr
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    val before_a : mr
    val a : int
    val after_a : mr
    |}]
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
  [%expect {| val x : 'a -> 'a |}];
  type_check_and_print ~with_fcp:true str;
  [%expect {| val x : 'a -> 'a |}]
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
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val b : unit
    val c : int
    val f : int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val b : unit
    val c : int
    val f : int
    |}]
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
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val g : mr -> unit
    val h : mr -> unit
    val i : mr -> unit
    val l : mr ref -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val g : mr -> unit
    val h : mr -> unit
    val i : mr -> unit
    val l : mr ref -> unit
    |}]
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
  [%expect
    {|
    error[E013]: ambiguous label
        ┌─ expect_test.ml:15:26
     15 │          ( { contents = { lbl = _ } } -> () )
        │                           ^^^
        = hint: add a type annotation
    |}];
  type_check_and_print ~defaulting:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val m : ms ref_repr -> unit
    |}]
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
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val n : mr ref_repr -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val n : mr ref_repr -> unit
    |}]
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
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val o : mr ref_repr -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val o : mr ref_repr -> unit
    |}]
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
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val r : mr ref -> int
    val s : mr ref -> unit
    val t : mr ref -> unit
    val u : mr ref -> int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      { lbl : int }
    type ms =
      { lbl : bool }
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val r : mr ref -> int
    val s : mr ref -> unit
    val t : mr ref -> unit
    val u : mr ref -> int
    |}]
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
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val before_a : mr
    val a : mr
    val b : unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val before_a : mr
    val a : mr
    val b : unit
    |}]
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
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val g : mr -> unit
    val h : mr -> unit
    val i : mr -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val g : mr -> unit
    val h : mr -> unit
    val i : mr -> unit
    |}]
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
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val l : mr ref -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val l : mr ref -> unit
    |}]
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
  [%expect
    {|
    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:22:24
     22 │          ( { contents = A } -> ()
        │                         ^
        = hint: add a type annotation

    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:23:24
     23 │          | { contents = B } -> ()
        │                         ^
        = hint: add a type annotation
    |}];
  type_check_and_print ~defaulting:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val m : ms ref -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val m : ms ref -> unit
    |}]
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
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val n : mr ref -> unit
    val o : mr ref -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val n : mr ref -> unit
    val o : mr ref -> unit
    |}]
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
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val s : mr ref -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val s : mr ref -> unit
    |}]
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
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val t : mr ref -> unit
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type mr =
      | A
      | B
    type ms =
      | A
      | B
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'a -> 'a ref
    external get_ref : 'b ref -> 'b
    external set_ref : 'c ref -> 'c -> unit
    external ref_repr : 'd ref -> 'd ref_repr
    val t : mr ref -> unit
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let xs = (1, 2, 3);;

      let x3 = xs.3;;

      let x3' = (1, 2, 3).3;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val xs : int * int * int
    val x3 : int
    val x3' : int
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val xs : int * int * int
    val x3 : int
    val x3' : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let f = fun x ->
        let result = x.2 in
        let useless = (x : int * int) in
        result
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| val f : int * int -> int |}];
  type_check_and_print ~with_fcp:true str;
  [%expect {| val f : int * int -> int |}]
;;

let%expect_test "" =
  let str =
    {|
      let g =
        let f = fun x -> x.1 in
        f (1, 2)
      ;;
    |}
  in
  type_check_and_print str;
  [%expect {| val g : int |}];
  type_check_and_print ~with_fcp:true str;
  [%expect {| val g : int |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;; 
      let pid = [ id : 'a. 'a -> 'a ] ;; 
      let see_pid = (fun x -> (@[x], @[x])) pid ;;
      let see_pid_type = forall (type 'a 'b) -> (see_pid : ('a -> 'a) * ('b -> 'b)) ;; 
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid : ['b. 'b -> 'b]
    val see_pid : ('c -> 'c) * ('d -> 'd)
    val see_pid_type : ('e -> 'e) * ('f -> 'f)
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid : ['b. 'b -> 'b]
    val see_pid : ('c -> 'c) * ('d -> 'd)
    val see_pid_type : ('e -> 'e) * ('f -> 'f)
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;; 
      let pid1 = exists (type 'b) -> [ id : 'a. 'a * 'b -> 'a * 'b ] ;;
      let see_pid1 = (fun x -> (@[x], @[x])) pid1 ;;
      let see_pid1_type = forall (type 'a 'b 'c) -> (see_pid1 : ('a * 'b -> 'a * 'b) * ('c * 'b -> 'c * 'b)) ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid1 : ['c. 'c * 'b -> 'c * 'b]
    val see_pid1 : ('d * 'e -> 'd * 'e) * ('f * 'e -> 'f * 'e)
    val see_pid1_type : ('g * 'h -> 'g * 'h) * ('i * 'h -> 'i * 'h)
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a * 'b -> 'a * 'b
    val pid1 : ['d. 'd * 'c -> 'd * 'c]
    val see_pid1 : ('e * 'f -> 'e * 'f) * ('g * 'f -> 'g * 'f)
    val see_pid1_type : ('h * 'i -> 'h * 'i) * ('j * 'i -> 'j * 'i)
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;; 
      let pid1 = exists (type 'b) -> [ id : 'a. 'a * 'b -> 'a * 'b ] ;;
      let see_pid1 = (fun x -> (@[x], @[x])) pid1 ;;
      let see_pid1_type_wrong = forall (type 'a 'b 'c 'd) -> (see_pid1 : ('a * 'b -> 'a * 'b) * ('c * 'd -> 'c * 'd)) ;;
    |}
  in
  (* Bug in grace, this should print aligned with the ^^^^^^ *)
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:5:63
      5 │        let see_pid1_type_wrong = forall (type 'a 'b 'c 'd) -> (see_pid1 : ('a * 'b -> 'a * 'b) * ('c * 'd -> 'c * 'd)) ;;
        │                                                                ^^^^^^^^ `('a * 'b -> 'a * 'b) *
        │                                                                          ('c * 'b -> 'c * 'b)`
        │                                                                           is not equal to
        │                                                                         `('d * 'e -> 'd * 'e) *
        │                                                                          ('f * 'g -> 'f * 'g)`
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:4:39
      4 │        let see_pid1 = (fun x -> (@[x], @[x])) pid1 ;;
        │                                        ^^^^ `'a * 'b -> 'a * 'b`
        │                                               is not equal to
        │                                             `'c * 'd -> 'c * 'd`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;; 
      let pid2 = [ id : 'a 'b. 'a * 'b -> 'a * 'b ] ;;
      let see_pid2 = (fun x -> (@[x], @[x])) pid2 ;;
      let see_pid2_type = forall (type 'a 'b 'c 'd) -> (see_pid2 : ('a * 'b -> 'a * 'b) * ('c * 'd -> 'c * 'd)) ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid2 : ['b 'c. 'b * 'c -> 'b * 'c]
    val see_pid2 : ('d * 'e -> 'd * 'e) * ('f * 'g -> 'f * 'g)
    val see_pid2_type : ('h * 'i -> 'h * 'i) * ('j * 'k -> 'j * 'k)
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a * 'b -> 'a * 'b
    val pid2 : ['c 'd. 'c * 'd -> 'c * 'd]
    val see_pid2 : ('e * 'f -> 'e * 'f) * ('g * 'h -> 'g * 'h)
    val see_pid2_type : ('i * 'j -> 'i * 'j) * ('k * 'l -> 'k * 'l)
    |}]
;;

let%expect_test "" =
  let str =
    {|
      external combine : 'a. 'a -> 'a -> 'a;;

      let id = fun x -> x ;; 
      let qid = [ id ] ;; 
      let pid = [ id : 'a. 'a -> 'a ] ;;
      let pqid = combine pid qid ;;
      let pqid_type = (pqid : [ 'a. 'a -> 'a ]) ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    external combine : 'a -> 'a -> 'a
    val id : 'b -> 'b
    val qid : ['c. 'c -> 'c]
    val pid : ['d. 'd -> 'd]
    val pqid : ['e. 'e -> 'e]
    val pqid_type : ['f. 'f -> 'f]
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    external combine : 'a -> 'a -> 'a
    val id : 'b -> 'b
    val qid : ['c. 'c -> 'c]
    val pid : ['d. 'd -> 'd]
    val pqid : ['e. 'e -> 'e]
    val pqid_type : ['f. 'f -> 'f]
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;;
      let mono_use_pid = fun pid -> @[pid] ;;
      let succ = fun x -> x + 1 ;;
      let mono_use_pid_app_succ = fun pid -> @[pid] succ ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E016]: unknown polytype
        ┌─ expect_test.ml:3:39
      3 │        let mono_use_pid = fun pid -> @[pid] ;;
        │                                        ^^^
        = hint: add a type annotation

    error[E016]: unknown polytype
        ┌─ expect_test.ml:5:48
      5 │        let mono_use_pid_app_succ = fun pid -> @[pid] succ ;;
        │                                                 ^^^
        = hint: add a type annotation
    |}];
  type_check_and_print ~defaulting:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val mono_use_pid : ['b] -> 'b
    val succ : int -> int
    val mono_use_pid_app_succ : [(int -> int) -> 'c] -> 'c
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val mono_use_pid : ['b] -> 'b
    val succ : int -> int
    val mono_use_pid_app_succ : [(int -> int) -> 'c] -> 'c
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;;
      let pid = [ id : 'a. 'a -> 'a ] ;; 
      let use_id_pid = (fun pid -> @[pid]) pid ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid : ['b. 'b -> 'b]
    val use_id_pid : 'c -> 'c
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid : ['b. 'b -> 'b]
    val use_id_pid : 'c -> 'c
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;;
      let pid = [ id : 'a. 'a ] ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:19
      3 │        let pid = [ id : 'a. 'a ] ;;
        │                    ^^ `'a -> 'a`
        │                         is not equal to
        │                       `'b`
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:19
      3 │        let pid = [ id : 'a. 'a ] ;;
        │                    ^^ `'a -> 'b`
        │                         is not equal to
        │                       `'c`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let succ = fun x -> x + 1 ;;
      let pid = [ succ : 'a. 'a -> 'a ] ;;  
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:19
      3 │        let pid = [ succ : 'a. 'a -> 'a ] ;;
        │                    ^^^^ `int -> int`
        │                           is not equal to
        │                         `'a -> 'a`
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:2:27
      2 │        let succ = fun x -> x + 1 ;;
        │                            ^^^^^ `int`
        │                                    is not equal to
        │                                  `'a`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;;
      let pid = [ id : 'a. 'a -> 'a ] ;;
      let use_id_twice_app_pid = (fun pid -> let x = @[pid] in (x, x)) pid ;;
      let xx_pid = (fun pid -> @[pid] @[pid]) pid ;;
      let idide = fun (pid : ['a. 'a -> 'a]) -> let id = @[pid] in (id, id) ;;
      let idide_pid = idide pid ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid : ['b. 'b -> 'b]
    val use_id_twice_app_pid : ('d -> 'd) * ('e -> 'e)
    val xx_pid : 'f -> 'f
    val idide : ['h. 'h -> 'h] -> ('i -> 'i) * ('j -> 'j)
    val idide_pid : ('k -> 'k) * ('l -> 'l)
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val pid : ['b. 'b -> 'b]
    val use_id_twice_app_pid : ('d -> 'd) * ('e -> 'e)
    val xx_pid : 'f -> 'f
    val idide : ['h. 'h -> 'h] -> ('i -> 'i) * ('j -> 'j)
    val idide_pid : ('k -> 'k) * ('l -> 'l)
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;;
      let use_poly_mono = fun x -> let y = [ (id, x) ] in @[y] ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E016]: unknown polytype
        ┌─ expect_test.ml:3:46
      3 │        let use_poly_mono = fun x -> let y = [ (id, x) ] in @[y] ;;
        │                                               ^^^^^^^
        = hint: add a type annotation

    error[E016]: unknown polytype
        ┌─ expect_test.ml:3:61
      3 │        let use_poly_mono = fun x -> let y = [ (id, x) ] in @[y] ;;
        │                                                              ^
        = hint: add a type annotation
    |}];
  type_check_and_print ~defaulting:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val use_poly_mono : 'c -> ('d -> 'd) * 'c
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val use_poly_mono : 'c -> ('d -> 'd) * 'c
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let id = fun x -> x ;;
      let use_poly_mono = fun x -> let y = [ (id, x) ] in 0 ;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E016]: unknown polytype
        ┌─ expect_test.ml:3:46
      3 │        let use_poly_mono = fun x -> let y = [ (id, x) ] in 0 ;;
        │                                               ^^^^^^^
        = hint: add a type annotation
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    val id : 'a -> 'a
    val use_poly_mono : 'c -> int
    |}]
;;

(** Module for incrementally building up test code, like adding to a file *)
module Incremental_test = struct
  type t =
    { mutable curr_input : string
    ; mutable curr_output : string
    ; test_fn : string -> unit
    }

  let create ?(initial = "") test_fn =
    test_fn initial;
    let curr_output =
      Ppx_expect_runtime.For_external.read_current_test_output_exn ~here:[%here]
    in
    Fmt.pr "%s%!" curr_output;
    { curr_input = initial; curr_output; test_fn }
  ;;

  let run t ?(add = false) str =
    let next_input = t.curr_input ^ str in
    t.test_fn next_input;
    let next_output =
      Ppx_expect_runtime.For_external.read_current_test_output_exn ~here:[%here]
    in
    (* Print output *)
    (match String.chop_prefix next_output ~prefix:t.curr_output with
     | None -> Fmt.pr "%s%!" next_output
     | Some chopped_next_output ->
       Fmt.pr "%s%!" chopped_next_output;
       (* Test was likely successful! Update output accordingly :D *)
       if add then t.curr_output <- next_output);
    if add then t.curr_input <- next_input
  ;;
end

let%expect_test "" =
  let test =
    Incremental_test.create
      ~initial:(include_fix ^ include_ref ^ include_option ^ include_list)
      (type_check_and_print ~defaulting:true)
  in
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'c -> 'c ref
    external get_ref : 'd ref -> 'd
    external set_ref : 'e ref -> 'e -> unit
    external ref_repr : 'f ref -> 'f ref_repr
    type 'a option =
      | None
      | Some of 'a
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    |}];
  let do_test = Incremental_test.run test in
  do_test
    ~add:true
    {|
      let poly1 = fun (id : [ 'a. 'a -> 'a ]) -> 
        let id = @[id] in
        (id 3, id true) 
      ;;
    |};
  [%expect {| val poly1 : ['h. 'h -> 'h] -> int * bool |}];
  do_test
    {|
      let xignore = poly1 [(fun x -> x)];;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly1 [(fun x -> x + 1)];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:25:29
     25 │        let xignore = poly1 [(fun x -> x + 1)];;
        │                              ^^^^^^^^^^^^^^ `int -> int`
        │                                               is not equal to
        │                                             `'a -> 'a`
    |}];
  do_test
    ~add:true
    {|
      let id = fun x -> x;;
      let xignore = poly1 [id];;
    |};
  [%expect
    {|
    val id : 'i -> 'i
    val xignore : int * bool
    |}];
  (* This is ill-typed in OCaml, since [id (fun x -> x)] is expansive.
     We don't have the value restriction in OmniML. *)
  do_test
    {|
      let xignore = poly1 [id (fun x -> x)];;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly1 [(let r = create_ref None in fun x -> set_ref r (Some x); x)];;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let escape = fun f -> poly1 [(fun x -> f x; x)];;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:28:37
     28 │        let escape = fun f -> poly1 [(fun x -> f x; x)];;
        │                                      ^^^^^^^^^^^^^^^
    |}];
  do_test
    ~add:true
    {|
      let poly2 = fun id ->
        let id = @[(id : ['a. 'a -> 'a])] in
        ((id 1, id true) : int * bool)
      ;;
    |};
  [%expect {| val poly2 : ['k. 'k -> 'k] -> int * bool |}];
  do_test
    {|
      let xignore = poly2 [(fun x -> x)];;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly2 [(fun x -> x + 1)];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:33:29
     33 │        let xignore = poly2 [(fun x -> x + 1)];;
        │                              ^^^^^^^^^^^^^^ `int -> int`
        │                                               is not equal to
        │                                             `'a -> 'a`
    |}];
  do_test
    ~add:true
    {|
      let poly3 = 
        forall (type 'b) ->
          fun (id : ['a. 'a -> 'a]) (x : ['b]) ->
            let id = @[id] in
            let x = @[x] in
            ((id x, id (Some x)) : 'b * 'b option)
      ;;
    |};
  [%expect {| val poly3 : ['n. 'n -> 'n] -> ['o] -> 'o * 'o option |}];
  do_test
    {|
      let xignore = poly3 [(fun x -> x)] [8];;
    |};
  [%expect {| val xignore : int * int option |}];
  do_test
    {|
      let xignore = poly3 [(fun x -> x + 1)] [8];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:41:29
     41 │        let xignore = poly3 [(fun x -> x + 1)] [8];;
        │                              ^^^^^^^^^^^^^^ `int -> int`
        │                                               is not equal to
        │                                             `'a -> 'a`
    |}];
  do_test
    ~add:true
    {|
      let poly4 = fix (fun poly4 p (id : ['a. 'a -> 'a]) ->
        let p = @[p] in
        let id = @[id] in
        if p then poly4 [false] [id] else (id 4, id true))
      ;;
    |};
  [%expect {| val poly4 : [bool] -> ['q. 'q -> 'q] -> int * bool |}];
  do_test
    {|
      let xignore = poly4 [true] [(fun x -> x)];;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly4 [true] [(fun x -> x + 1)];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:47:36
     47 │        let xignore = poly4 [true] [(fun x -> x + 1)];;
        │                                     ^^^^^^^^^^^^^^ `int -> int`
        │                                                      is not equal to
        │                                                    `'a -> 'a`
    |}];
  do_test
    ~add:true
    {|
      let poly5 = fix (fun poly5 (p : [bool]) (id : ['a. 'a -> 'a]) -> 
        let p = @[p] in
        let id = @[id] in
        ((if p then poly5 [false] [id] else (id 5, id true)) : int * bool))
      ;;
    |};
  [%expect {| val poly5 : [bool] -> ['s. 's -> 's] -> int * bool |}];
  do_test
    {|
      let xignore = poly5 [true] [(fun x -> x)];;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly5 [true] [(fun x -> x + 1)];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:53:36
     53 │        let xignore = poly5 [true] [(fun x -> x + 1)];;
        │                                     ^^^^^^^^^^^^^^ `int -> int`
        │                                                      is not equal to
        │                                                    `'a -> 'a`
    |}];
  do_test
    ~add:true
    {|
      let poly6 = forall (type 'b) -> 
        fix (fun poly6 -> 
          fun (p : [bool]) (id : ['a. 'a -> 'a]) (x : ['b]) ->
            let p = @[p] in
            let id = @[id] in
            let x = @[x] in
            ((if p then poly6 [false] [id] [x] else (id x, id (Some x))) : 'b * 'b option))
      ;;
    |};
  [%expect {| val poly6 : [bool] -> ['v. 'v -> 'v] -> ['w] -> 'w * 'w option |}];
  do_test
    {|
      let xignore = poly6 [true] [(fun x -> x)] [8];; 
    |};
  [%expect {| val xignore : int * int option |}];
  do_test
    {|
      let xignore = poly6 [true] [(fun x -> x + 1)] [8];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:62:36
     62 │        let xignore = poly6 [true] [(fun x -> x + 1)] [8];;
        │                                     ^^^^^^^^^^^^^^ `int -> int`
        │                                                      is not equal to
        │                                                    `'a -> 'a`
    |}];
  do_test
    ~add:true
    {|
      let needs_magic = fun (magic : ['a 'b. 'a -> 'b]) ->
        let magic = @[magic] in
        (magic 5 : bool)
      ;;
    |};
  [%expect {| val needs_magic : ['z 'a1. 'a1 -> 'z] -> bool |}];
  do_test
    {|
      let xignore = needs_magic [(fun x -> x)];;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:67:35
     67 │        let xignore = needs_magic [(fun x -> x)];;
        │                                    ^^^^^^^^^^ `'a -> 'a`
        │                                                 is not equal to
        │                                               `'b -> 'c`
    |}];
  do_test
    ~add:true
    {|
      let with_id = forall (type 'b) -> fun (f : [['a. 'a -> 'a] -> 'b]) ->
        let f = @[f] in
        (f [(fun x -> x)] : 'b)
      ;;
    |};
  [%expect {| val with_id : [['d1. 'd1 -> 'd1] -> 'e1] -> 'e1 |}];
  do_test
    {|
      let xignore = with_id [(fun id -> 
        let id = @[id] in
        (id 1, id true))] 
      ;;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let non_principal1 = fun p f ->
        let p = @[p] in
        let f = @[f] in
        if p then with_id [f] else f [(fun x -> x)]
      ;;
    |};
  [%expect {| val non_principal1 : [bool] -> [['h1. 'h1 -> 'h1] -> 'g1] -> 'g1 |}];
  do_test
    {|
      let non_principal2 = fun p f ->
        let p = @[p] in
        let f = @[f] in
        if p then f [(fun x -> x)] else with_id [f]
      ;;
    |};
  [%expect {| val non_principal2 : [bool] -> [['h1. 'h1 -> 'h1] -> 'g1] -> 'g1 |}];
  do_test
    {|
      let principal1 = exists (type 'b) -> fun p (f : [['a. 'a -> 'a] -> 'b]) ->
        let p = @[p] in
        let f = @[f] in
        if p then f [(fun x -> x)] else with_id [f]
      ;;
    |};
  [%expect {| val principal1 : [bool] -> [['h1. 'h1 -> 'h1] -> 'g1] -> 'g1 |}];
  do_test
    {|
      let principal2 = exists (type 'b) -> 
        (fun p f -> 
          let p = @[p] in
          let f = @[f] in
          if p then f [(fun x -> x)] else with_id [f] 
        : [bool] -> [['a. 'a -> 'a] -> 'b] -> 'b)
      ;;
    |};
  [%expect {| val principal2 : [bool] -> [['h1. 'h1 -> 'h1] -> 'g1] -> 'g1 |}];
  do_test
    {|
      let principal3 = ( 
        Cons (None, Cons (Some (fun x -> 
          let x = @[x] in
          (x 5, x true)), Nil))
        : (['a. 'a -> 'a] -> int * bool) option list)
      ;;
    |};
  [%expect {| val principal3 : (['g1. 'g1 -> 'g1] -> int * bool) option list |}];
  do_test
    {|
      let non_principal3 = 
        Cons ((Some (fun x -> let x = @[x] in (x 5, x true)) : (['a. 'a -> 'a] -> int * bool) option), 
        Cons (Some (fun x -> let x = @[x] in (x 6, x false)), Nil))
      ;;
    |};
  [%expect {| val non_principal3 : (['h1. 'h1 -> 'h1] -> int * bool) option list |}];
  do_test
    {|
      let non_principal4 = 
        Cons ((Some (fun x -> let x = @[x] in (x 5, x true))), 
        Cons ((Some (fun x -> let x = @[x] in (x 6, x false)) : (['a. 'a -> 'a] -> int * bool) option), Nil))
      ;;
    |};
  [%expect {| val non_principal4 : (['h1. 'h1 -> 'h1] -> int * bool) option list |}];
  do_test
    {|
      let foo = fun (f : [['a. 'a -> 'a] -> int]) -> 
        let f = @[f] in
        (fun id -> 
          let id = @[id] in
          f [id]
        : ['a 'b. 'a -> 'b] -> int)
      ;;
    |};
  [%expect {| val foo : [['i1. 'i1 -> 'i1] -> int] -> ['j1 'k1. 'k1 -> 'j1] -> int |}]
;;

let%expect_test "" =
  let test =
    Incremental_test.create
      ~initial:(include_fix ^ include_ref ^ include_option ^ include_list)
      (type_check_and_print ~with_fcp:true)
  in
  [%expect
    {|
    external fix : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    type 'a ref
    type 'a ref_repr =
      { contents : 'a }
    external create_ref : 'c -> 'c ref
    external get_ref : 'd ref -> 'd
    external set_ref : 'e ref -> 'e -> unit
    external ref_repr : 'f ref -> 'f ref_repr
    type 'a option =
      | None
      | Some of 'a
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    |}];
  let do_test = Incremental_test.run test in
  do_test
    ~add:true
    {|
      let poly1 = fun (forall id : 'a. 'a -> 'a) ->
        (id 1, id true)
      ;;
    |};
  [%expect {| val poly1 : (forall 'g. 'g -> 'g) -> int * bool |}];
  do_test
    {|
      let xignore = poly1 (fun x -> x);;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly1 (fun x -> x + 1);;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:24:37
     24 │        let xignore = poly1 (fun x -> x + 1);;
        │                                      ^^^^^ `int`
        │                                              is not equal to
        │                                            `'a`
    |}];
  do_test
    ~add:true
    {|
      let id = fun x -> x;;
    |};
  [%expect {| val id : 'h -> 'h |}];
  do_test
    {|
      let xignore = poly1 id;;
    |};
  [%expect {| val xignore : int * bool |}];
  (* Passes in OmniML since we don't have the value restriction, 
     but fails in OCaml *)
  do_test
    {|
      let xignore = poly1 (id (fun x -> x));;
    |};
  [%expect {| val xignore : int * bool |}];
  (* Ditto *)
  do_test
    {|
      let xignore = poly1 (let r = create_ref None in fun x -> set_ref r (Some x); x);;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let escape = fun f -> poly1 (fun x -> f x; x);;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:26:36
     26 │        let escape = fun f -> poly1 (fun x -> f x; x);;
        │                                     ^^^^^^^^^^^^^^^
    |}];
  do_test
    ~add:true
    {|
      let poly2 = fun (forall id : 'a. 'a -> 'a) ->
        ((id 1, id true) : int * bool)
      ;;
    |};
  [%expect {| val poly2 : (forall 'i. 'i -> 'i) -> int * bool |}];
  do_test
    {|
      let xignore = poly2 (fun x -> x);;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly2 (fun x -> x + 1);;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:30:37
     30 │        let xignore = poly2 (fun x -> x + 1);;
        │                                      ^^^^^ `int`
        │                                              is not equal to
        │                                            `'a`
    |}];
  do_test
    ~add:true
    {|
      let poly3 = 
        forall (type 'b) ->
          fun (forall id : 'a. 'a -> 'a) (x : 'b) ->
            ((id x, id (Some x)) : 'b * 'b option)
      ;;
    |};
  [%expect {| val poly3 : (forall 'j. 'j -> 'j) -> 'k -> 'k * 'k option |}];
  do_test
    {|
      let xignore = poly3 (fun x -> x) 8;;
    |};
  [%expect {| val xignore : int * int option |}];
  do_test
    {|
      let xignore = poly3 (fun x -> x + 1) 8;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:36:37
     36 │        let xignore = poly3 (fun x -> x + 1) 8;;
        │                                      ^^^^^ `int`
        │                                              is not equal to
        │                                            `'a`
    |}];
  do_test
    ~add:true
    {|
      let poly4 = fix (fun poly4 p (forall id : 'a. 'a -> 'a) ->
        if p then poly4 false id else (id 4, id true))
      ;;
    |};
  [%expect {| val poly4 : bool -> (forall 'l. 'l -> 'l) -> int * bool |}];
  do_test
    {|
      let xignore = poly4 true (fun x -> x);;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly4 true (fun x -> x + 1);;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:1:1
      1 │ ╭  external fix : 'a 'b. (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b;;
      2 │ │      type 'a ref;;
        · │
     40 │ │        let xignore = poly4 true (fun x -> x + 1);;
     41 │ │
        │ ╰─────^ `int`
        │           is not equal to
        │         `'a`
    |}];
  do_test
    ~add:true
    {|
      let poly5 = fix (fun poly5 (p : bool) (forall id : 'a. 'a -> 'a) -> 
        ((if p then poly5 false id else (id 5, id true)) : int * bool))
      ;;
    |};
  [%expect {| val poly5 : bool -> (forall 'm. 'm -> 'm) -> int * bool |}];
  do_test
    {|
      let xignore = poly5 true (fun x -> x);;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let xignore = poly5 true (fun x -> x + 1);;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:44:42
     44 │        let xignore = poly5 true (fun x -> x + 1);;
        │                                           ^^^^^ `int`
        │                                                   is not equal to
        │                                                 `'a`
    |}];
  do_test
    ~add:true
    {|
      let poly6 = forall (type 'b) -> 
        fix (fun poly6 -> 
          fun (p : bool) (forall id : 'a. 'a -> 'a) (x : 'b) ->
            ((if p then poly6 false id x else (id x, id (Some x))) : 'b * 'b option))
      ;;
    |};
  [%expect {| val poly6 : bool -> (forall 'n. 'n -> 'n) -> 'o -> 'o * 'o option |}];
  do_test
    {|
      let xignore = poly6 true (fun x -> x) 8;; 
    |};
  [%expect {| val xignore : int * int option |}];
  do_test
    {|
      let xignore = poly6 true (fun x -> x + 1) 8;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:50:42
     50 │        let xignore = poly6 true (fun x -> x + 1) 8;;
        │                                           ^^^^^ `int`
        │                                                   is not equal to
        │                                                 `'a`
    |}];
  do_test
    ~add:true
    {|
      let needs_magic = fun (forall magic : 'a 'b. 'a -> 'b) ->
        (magic 5 : bool)
      ;;
    |};
  [%expect {| val needs_magic : (forall 'p 'q. 'q -> 'p) -> bool |}];
  do_test
    {|
      let xignore = needs_magic (fun x -> x);;
    |};
  (* Womp, no location for this unification error :// *)
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:1:1
      1 │ ╭  external fix : 'a 'b. (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b;;
      2 │ │      type 'a ref;;
        · │
     54 │ │        let xignore = needs_magic (fun x -> x);;
     55 │ │
        │ ╰─────^ `'a`
        │           is not equal to
        │         `'b`
    |}];
  do_test
    ~add:true
    {|
      let with_id = forall (type 'b) -> fun (f : ((forall 'a. 'a -> 'a) -> 'b)) ->
        (f (fun x -> x) : 'b)
      ;;
    |};
  [%expect {| val with_id : ((forall 'r. 'r -> 'r) -> 's) -> 's |}];
  do_test
    {|
      let xignore = with_id (fun id -> 
        (id 1, id true)) 
      ;;
    |};
  [%expect {| val xignore : int * bool |}];
  do_test
    {|
      let non_principal1 = fun p f ->
        if p then with_id f else f (fun x -> x)
      ;;
    |};
  [%expect {| val non_principal1 : bool -> ((forall 't. 't -> 't) -> 'u) -> 'u |}];
  do_test
    {|
      let non_principal2 = fun p f ->
        if p then f (fun x -> x) else with_id f
      ;;
    |};
  [%expect {| val non_principal2 : bool -> ((forall 't. 't -> 't) -> 'u) -> 'u |}];
  do_test
    {|
      let principal1 = exists (type 'b) -> fun p (f : (forall 'a. 'a -> 'a) -> 'b) ->
        if p then f (fun x -> x) else with_id f
      ;;
    |};
  [%expect {| val principal1 : bool -> ((forall 't. 't -> 't) -> 'u) -> 'u |}];
  do_test
    {|
      let principal2 = exists (type 'b) -> 
        (fun p f -> 
          if p then f (fun x -> x) else with_id f 
        : bool -> ((forall 'a. 'a -> 'a) -> 'b) -> 'b)
      ;;
    |};
  [%expect {| val principal2 : bool -> ((forall 't. 't -> 't) -> 'u) -> 'u |}];
  do_test
    {|
      let principal3 = ( 
        Cons (None, Cons (Some (fun x -> 
          (x 5, x true)), Nil))
        : ((forall 'a. 'a -> 'a) -> int * bool) option list)
      ;;
    |};
  [%expect {| val principal3 : ((forall 't. 't -> 't) -> int * bool) option list |}];
  do_test
    {|
      let non_principal3 = 
        Cons ((Some (fun x -> (x 5, x true)) : ((forall 'a. 'a -> 'a) -> int * bool) option), 
        Cons (Some (fun x -> (x 6, x false)), Nil))
      ;;
    |};
  [%expect {| val non_principal3 : ((forall 't. 't -> 't) -> int * bool) option list |}];
  do_test
    {|
      let non_principal4 = 
        Cons ((Some (fun x -> (x 5, x true))), 
        Cons ((Some (fun x -> (x 6, x false)) : ((forall 'a. 'a -> 'a) -> int * bool) option), Nil))
      ;;
    |};
  [%expect {| val non_principal4 : ((forall 't. 't -> 't) -> int * bool) option list |}];
  do_test
    {|
      let foo = fun (f : (forall 'a. 'a -> 'a) -> int) -> 
        (fun id -> f id
        : (forall 'a 'b. 'a -> 'b) -> int)
      ;;
    |};
  [%expect
    {| val foo : ((forall 't. 't -> 't) -> int) -> (forall 'u 'v. 'v -> 'u) -> int |}]
;;

let%expect_test "" =
  let str =
    {|
      let (x, y) = (1, true);; 
      let _ = y + 1;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:15
      3 │        let _ = y + 1;;
        │                ^ `bool`
        │                    is not equal to
        │                  `int`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let ((x, y), z) = ((1, 2), true);; 
      let _ = x + y;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val x : int
    val y : int
    val z : bool
    |}]
;;

let%expect_test "" =
  let str =
    include_option
    ^ {|
      let Some x = Some 5;; 
      let _ = x + 1;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a option =
      | None
      | Some of 'a
    val x : int
    |}]
;;

let%expect_test "" =
  let str =
    include_option
    ^ {|
      let Some (x, y) = Some (1, true);;
      let _ = x + 1;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a option =
      | None
      | Some of 'a
    val x : int
    val y : bool
    |}]
;;

let%expect_test "" =
  let str =
    include_option
    ^ {|
      let (Some x, Some y) = (Some 1, Some 2);; 
      let _ = x + y;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a option =
      | None
      | Some of 'a
    val x : int
    val y : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let ((x, y) : int * bool) = (1, true);;
      let _ = x + 1;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val x : int
    val y : bool
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let ((x : int), (y : bool)) = (1, true);;
      let _ = x + 1;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val x : int
    val y : bool
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let _ = 1 + 1;;
    |}
  in
  type_check_and_print str;
  [%expect {| |}]
;;

let%expect_test "" =
  let str =
    {|
      let (_, y) = (1, true);; 
      let _ = y;;
    |}
  in
  type_check_and_print str;
  [%expect {| val y : bool |}]
;;

let%expect_test "" =
  let str =
    {|
      let ((x, y) as p) = (1, true);;
      let _ = p;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val p : int * bool
    val x : int
    val y : bool
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let ((x, y) as p) = (1, true);;
      let _ = (x, y, p);;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    val p : int * bool
    val x : int
    val y : bool
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type 'a tree =
        | Leaf
        | Node of 'a * 'a tree * 'a tree
      ;;

      let Node (v, l, r) = Node (5, Leaf, Leaf);;
      let _ = v + 2;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a tree =
      | Leaf
      | Node of 'a * 'a tree * 'a tree
    val l : int tree
    val r : int tree
    val v : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let (x, y) = (1, 2, 3);;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:2:11
      2 │        let (x, y) = (1, 2, 3);;
        │            ^^^^^^ `int * int * int`
        │                     is not equal to
        │                   `'a * 'b`
    |}]
;;

let%expect_test "" =
  let str =
    include_option
    ^ {|
      let Some x = None;;
      let _ = (x : int);;
      let _ = (x : bool);;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a option =
      | None
      | Some of 'a
    val x : 'a
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let ((x : int), (y : bool)) = (true, 1);;
      let _ = x;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:2:11
      2 │        let ((x : int), (y : bool)) = (true, 1);;
        │            ^^^^^^^^^^^^^^^^^^^^^^^ `bool * int`
        │                                      is not equal to
        │                                    `int * bool`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let pair = fun x y -> (x, y);;
      let (x, y) = f 1 true;; 
      let _ = (x + 1, y);;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E004]: cannot find value `f` in this scope
        ┌─ expect_test.ml:3:20
      3 │        let (x, y) = f 1 true;;
        │                     ^ not found in this scope
    |}]
;;

let%expect_test "" =
  let str =
    include_list
    ^ {|
      let pair = fun x y -> (x, y);;
      let Cons ((x, y), Cons ((z, w), Nil)) = 
        Cons (pair 1 true, Cons (pair 2 false, Nil))
      ;;
      let _ = x + z;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    val pair : 'a -> 'b -> 'a * 'b
    val w : bool
    val x : int
    val y : bool
    val z : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type point = { x : int; y : int };;
      let { x = a; y = b } = { x = 1; y = 2 };;
      let _ = a + b;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type point =
      { x : int; y : int }
    val a : int
    val b : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type point = { x : int; y : int };;
      let { x = a; y = b } = { x = 1; y = true };;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:3:43
      3 │        let { x = a; y = b } = { x = 1; y = true };;
        │                                            ^^^^ `int`
        │                                                   is not equal to
        │                                                 `bool`
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type point = { x : int; y : int };;
      type point3d = { x : int; y : int; z : int };;
      let { x = a; y = b } = { x = 1; y = 2; z = 3 };;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type point =
      { x : int; y : int }
    type point3d =
      { x : int; y : int; z : int }
    val a : int
    val b : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let poly_pattern = fun (forall (id1, id2) : 'a 'b. ('a -> 'a) * ('b -> 'b)) -> 
        let _ = id1 1 in
        let _ = id1 true in
        let _ = id2 1 in
        let _ = id2 true in
        ()
      ;;
    |}
  in
  type_check_and_print ~with_fcp:true str;
  [%expect {| val poly_pattern : (forall 'a 'b. ('a -> 'a) * ('b -> 'b)) -> unit |}]
;;

let%expect_test "" =
  (* All examples from https://dl.acm.org/doi/pdf/10.1145/3408971 *)
  (* The following compares results from QuickLook. We 
     primarily use the manual encoding of OCaml's polyparams into polytypes: 
       [[ fun x -> e ]] = fun x -> let x = @[ x ] in [[ e ]]
       [[ e1 e2 ]] = [[ e1 ]] [ [[ e2 ]] ] *)
  (* Some special attention is given to higher-rank poly that doesn't 
     fit into polyparams -- e.g. E1b *)
  let str =
    include_list
    ^ {|
      external head : 'a. 'a list -> 'a;;
      external tail : 'a. 'a list -> 'a list;;
      external single : 'a. 'a -> 'a list;;
      external concat : 'a. 'a list -> 'a list -> 'a list;;
      external length : 'a. 'a list -> int;;
      external id : 'a. 'a -> 'a;;
      external ids : [ 'a. 'a -> 'a ] list;;
      external map : 'a 'b. ('a -> 'b) -> 'a list -> 'b list;;
      external app : 'a 'b. ('a -> 'b) -> 'a -> 'b;;
      external revapp : 'a 'b. 'a -> ('a -> 'b) -> 'b;;
      external poly : [ 'a. 'a -> 'a ] -> int * bool;;
      external inc : int -> int;;
      external incs : (int -> int) list;;
      external choose : 'a. 'a -> 'a -> 'a;;
      external auto : [ 'a. 'a -> 'a ] -> [ 'a. 'a -> 'a ];;
      external auto2 : 'b. [ 'a. 'a -> 'a ] -> 'b -> 'b;;
      external compose : 'a 'b 'c. ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c;;

      let const2 = fun x y -> x;;

      let a1 = const2;;
      let a2 = choose id;; 
      let a3 = choose Nil ids;;
      let a4 = fun x -> 
        let x = @[(x : [ 'a. 'a -> 'a ])] in 
        x x 
      ;;
      let a5 = id auto;; 
      let a6 = id auto2;; 
      let a7 = choose id auto;; 

      (* The following is ill-typed *)
      (* let a8 = choose id auto2;; *)
      (* with error:
         error[E011]: mismatched type
            ┌─ expect_test.ml:32:26
         32 │        let a8 = choose id auto2;;
            │                           ^^^^^ `(ν. 'a. 'a -> 'a) -> 'a -> 'a`
            │                                   is not equal to
            │                                 `'b -> 'b`
      *)

      (* The following is ill-typed *)
      (* external f : 'a. ('a -> 'a) -> 'a list -> 'a;; *)
      (* let a9 = f (choose id) ids ;; *)
      (* with error: 
         error[E011]: mismatched type
             ┌─ expect_test.ml:43:30
          43 │        let a9 = f (choose id) ids ;;
             │                               ^^^ `((ν. 'a. 'a -> 'a)) list`
             │                                     is not equal to
             │                                   `('a -> 'a) list`
      *)
     
      let a10 = 
        (poly [id], poly [fun x -> x], id poly [fun x -> x]);;

      external k : 'a. 'a -> 'a list -> int;; 
      external xs : ([ 'a. 'a -> 'a ] -> int * bool ) list;; 
      let a11 = k (fun f -> let f = @[f] in (f 1, f true)) xs;;

      let a12 = 
        (poly [id], app poly [id], revapp [id] poly);;

      (* single id will have the monotype [('a -> 'a) list] *)
      let b1 = 
        (length ids, tail ids, head ids, single id)
      ;;

      let b2 = 
        Cons ([ id ], ids)
      ;;

      let b3 = 
        Cons ([ fun x -> x ], ids)
      ;;

      let b4 = 
        concat (single inc) (single id) 
      ;;

      let b5 = 
        map poly (single [ id ])
      ;;

      let b7 = 
        (map head (single ids), @[head ids] true)
      ;;
      
      (* Some more examples from the GI paper *)
      let b1 = 
        fun f -> 
          let f = @[( f : [ 'a. 'a -> 'a ])] in 
          (f 1, f true)
      ;;

      (* This is quite interesting, no other system typechecks this *)
      let b2 = 
        fun xs -> 
          poly (head xs)
      ;;

      let c1b = 
        fun (f : [ 'a. 'a -> 'a ]) -> 
          let f = @[f] in 
          (f 1, f true) 
      ;;

      type char;;
      external g : ([ 'a. 'a -> 'a ] -> int * bool) -> char;;
      let c1c = 
        g (fun f ->
          let f = @[f] in 
          (f 1, f true))
      ;;

      (* This is ill-typed ( we don't have an encoding for arbitrary-rank polymorphism ) *)
      (* external r : [ 'a. 'a -> [ 'b. 'b -> 'b ] ] -> int;; *)
      (* let c2 = r [ fun x -> fun y -> y ] ;; *)
      (* with error:
         error[E011]: mismatched type
             ┌─ expect_test.ml:83:11
          83 │          r [ fun x -> fun y -> y ]
             │            ^^^^^^^^^^^^^^^^^^^^^^^ `'a -> 'b -> 'b`
             │                                      is not equal to
             │                                    `'c -> (ν. 'a. 'a -> 'a)`
      *)

      external k : 'a. 'a -> 'a list -> 'a;;
      external h : int -> [ 'a. 'a -> 'a ];;
      external lst : [ 'a. int -> 'a -> 'a ] list;;

      (* This is ill-typed *)
      (* let e1a = k h lst;; *)

      let e1b = k [ (fun x -> @[ h x ]) ] lst;;

      let e2a = fun x -> poly x;;

      let e2b = (fun x -> poly x : [ 'a. 'a -> 'a ] -> int * bool);;

      let e3a = app poly [ id ];;

      let e3b = app (fun x -> poly x) [ id ];;

      let e4a = map poly ids;;

      let e4b = map (fun x -> poly x) ids;;

      let e5a = compose poly head;;

      let e5b = fun xs -> poly (head xs);;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external head : 'a list -> 'a
    external tail : 'b list -> 'b list
    external single : 'c -> 'c list
    external concat : 'd list -> 'd list -> 'd list
    external length : 'e list -> int
    external id : 'f -> 'f
    external ids : ['g. 'g -> 'g] list
    external map : ('h -> 'i) -> 'h list -> 'i list
    external app : ('j -> 'k) -> 'j -> 'k
    external revapp : 'l -> ('l -> 'm) -> 'm
    external poly : ['n. 'n -> 'n] -> int * bool
    external inc : int -> int
    external incs : (int -> int) list
    external choose : 'o -> 'o -> 'o
    external auto : ['p. 'p -> 'p] -> ['q. 'q -> 'q]
    external auto2 : ['r. 'r -> 'r] -> 's -> 's
    external compose : ('t -> 'u) -> ('v -> 't) -> 'v -> 'u
    val const2 : 'w -> 'x -> 'w
    val a1 : 'y -> 'z -> 'y
    val a2 : ('a1 -> 'a1) -> 'a1 -> 'a1
    val a3 : ['b1. 'b1 -> 'b1] list
    val a4 : ['d1. 'd1 -> 'd1] -> 'e1 -> 'e1
    val a5 : ['f1. 'f1 -> 'f1] -> ['g1. 'g1 -> 'g1]
    val a6 : ['h1. 'h1 -> 'h1] -> 'i1 -> 'i1
    val a7 : ['j1. 'j1 -> 'j1] -> ['k1. 'k1 -> 'k1]
    val a10 : (int * bool) * (int * bool) * (int * bool)
    external k : 'l1 -> 'l1 list -> int
    external xs : (['m1. 'm1 -> 'm1] -> int * bool) list
    val a11 : int
    val a12 : (int * bool) * (int * bool) * (int * bool)
    val b1 : int * ['o1. 'o1 -> 'o1] list * ['p1. 'p1 -> 'p1] * ('q1 -> 'q1) list
    val b2 : ['r1. 'r1 -> 'r1] list
    val b3 : ['s1. 's1 -> 's1] list
    val b4 : (int -> int) list
    val b5 : (int * bool) list
    val b7 : ['t1. 't1 -> 't1] list * bool
    val b1 : ['v1. 'v1 -> 'v1] -> int * bool
    val b2 : ['w1. 'w1 -> 'w1] list -> int * bool
    val c1b : ['y1. 'y1 -> 'y1] -> int * bool
    type char
    external g : (['z1. 'z1 -> 'z1] -> int * bool) -> char
    val c1c : char
    external k : 'b2 -> 'b2 list -> 'b2
    external h : int -> ['c2. 'c2 -> 'c2]
    external lst : ['d2. int -> 'd2 -> 'd2] list
    val e1b : ['e2. int -> 'e2 -> 'e2]
    val e2a : ['f2. 'f2 -> 'f2] -> int * bool
    val e2b : ['g2. 'g2 -> 'g2] -> int * bool
    val e3a : int * bool
    val e3b : int * bool
    val e4a : (int * bool) list
    val e4b : (int * bool) list
    val e5a : ['h2. 'h2 -> 'h2] list -> int * bool
    val e5b : ['i2. 'i2 -> 'i2] list -> int * bool
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external head : 'a list -> 'a
    external tail : 'b list -> 'b list
    external single : 'c -> 'c list
    external concat : 'd list -> 'd list -> 'd list
    external length : 'e list -> int
    external id : 'f -> 'f
    external ids : ['g. 'g -> 'g] list
    external map : ('h -> 'i) -> 'h list -> 'i list
    external app : ('j -> 'k) -> 'j -> 'k
    external revapp : 'l -> ('l -> 'm) -> 'm
    external poly : ['n. 'n -> 'n] -> int * bool
    external inc : int -> int
    external incs : (int -> int) list
    external choose : 'o -> 'o -> 'o
    external auto : ['p. 'p -> 'p] -> ['q. 'q -> 'q]
    external auto2 : ['r. 'r -> 'r] -> 's -> 's
    external compose : ('t -> 'u) -> ('v -> 't) -> 'v -> 'u
    val const2 : 'w -> 'x -> 'w
    val a1 : 'y -> 'z -> 'y
    val a2 : ('a1 -> 'a1) -> 'a1 -> 'a1
    val a3 : ['b1. 'b1 -> 'b1] list
    val a4 : ['d1. 'd1 -> 'd1] -> 'e1 -> 'e1
    val a5 : ['f1. 'f1 -> 'f1] -> ['g1. 'g1 -> 'g1]
    val a6 : ['h1. 'h1 -> 'h1] -> 'i1 -> 'i1
    val a7 : ['j1. 'j1 -> 'j1] -> ['k1. 'k1 -> 'k1]
    val a10 : (int * bool) * (int * bool) * (int * bool)
    external k : 'l1 -> 'l1 list -> int
    external xs : (['m1. 'm1 -> 'm1] -> int * bool) list
    val a11 : int
    val a12 : (int * bool) * (int * bool) * (int * bool)
    val b1 : int * ['o1. 'o1 -> 'o1] list * ['p1. 'p1 -> 'p1] * ('q1 -> 'q1) list
    val b2 : ['r1. 'r1 -> 'r1] list
    val b3 : ['s1. 's1 -> 's1] list
    val b4 : (int -> int) list
    val b5 : (int * bool) list
    val b7 : ['t1. 't1 -> 't1] list * bool
    val b1 : ['v1. 'v1 -> 'v1] -> int * bool
    val b2 : ['w1. 'w1 -> 'w1] list -> int * bool
    val c1b : ['y1. 'y1 -> 'y1] -> int * bool
    type char
    external g : (['z1. 'z1 -> 'z1] -> int * bool) -> char
    val c1c : char
    external k : 'b2 -> 'b2 list -> 'b2
    external h : int -> ['c2. 'c2 -> 'c2]
    external lst : ['d2. int -> 'd2 -> 'd2] list
    val e1b : ['e2. int -> 'e2 -> 'e2]
    val e2a : ['f2. 'f2 -> 'f2] -> int * bool
    val e2b : ['g2. 'g2 -> 'g2] -> int * bool
    val e3a : int * bool
    val e3b : int * bool
    val e4a : (int * bool) list
    val e4b : (int * bool) list
    val e5a : ['h2. 'h2 -> 'h2] list -> int * bool
    val e5b : ['i2. 'i2 -> 'i2] list -> int * bool
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type t = 
        | Foo of u

      and u = 
        | Foo of t
      ;;

      external unify : 'a. 'a -> 'a -> unit;;

      (* Cycles are possible with recursive overloaded variants *)
      let _ = 
        fun x y -> 
          unify x (Foo (y));
          unify y (Foo (x))
      ;;
    |}
  in
  type_check_and_print ~defaulting:true str;
  [%expect
    {|
    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:14:20
     14 │            unify x (Foo (y));
        │                     ^^^
        = hint: add a type annotation

    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:15:20
     15 │            unify y (Foo (x))
        │                     ^^^
        = hint: add a type annotation
    |}];
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:15:20
     15 │            unify y (Foo (x))
        │                     ^^^
        = hint: add a type annotation

    error[E010]: ambiguous constructor
        ┌─ expect_test.ml:14:20
     14 │            unify x (Foo (y));
        │                     ^^^
        = hint: add a type annotation
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let non_trivial_cycle = fun (f, g) -> (f g, g f);;
    |}
  in
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E016]: unknown polytype
        ┌─ expect_test.ml:2:51
      2 │        let non_trivial_cycle = fun (f, g) -> (f g, g f);;
        │                                                    ^^^
        = hint: add a type annotation

    error[E016]: unknown polytype
        ┌─ expect_test.ml:2:46
      2 │        let non_trivial_cycle = fun (f, g) -> (f g, g f);;
        │                                               ^^^
        = hint: add a type annotation

    error[E016]: unknown polytype
        ┌─ expect_test.ml:2:53
      2 │        let non_trivial_cycle = fun (f, g) -> (f g, g f);;
        │                                                      ^
        = hint: add a type annotation

    error[E016]: unknown polytype
        ┌─ expect_test.ml:2:48
      2 │        let non_trivial_cycle = fun (f, g) -> (f g, g f);;
        │                                                 ^
        = hint: add a type annotation
    |}]
;;

(*
   Why can cycles not occur in the defaulting of polyparams (without -rectypes)?

   Recall that the constraint generation function [[ e : 't ]] 
   for polyparams includes:

   [[ x : 't ]] = x 't

   [[ fun x -> e : 't ]] = 
     exists 'a 'b. 
     't = 'a -> 'b 
     && let x = \'c. <'a>([s] -> s <= 'c) ? mono in
        [[ e : 'b ]]


   [[ e1 e2 : 't ]] =
     exists 'a 'b.
     [[ e1 : 'a ]] 
     && 'a = 'b -> 't 
     && let arg = \'c. [[ e2 : 'c ]] in
        <'b>([s] -> arg <= s) ? mono

   We proceed by proof by contradiction. That is, let us assume 
   for some [[ e : 't ]] there is a cycle. Let us consider cases 
   on e. 

   We proceed by cases on `e`: 

     - e = x: No cycles, contradiction!

     - e = fun x -> e': 

       We have: 

       [[ e : 't ]] = 
         exists 'a 'b. 
         't = 'a -> 'b 
         && let x = \'c. <'a>([s] -> s <= 'c) ? mono in
            [[ e' : 'b ]]

       Two cases: 
       - <'a>([s] -> s <= 'c) ? mono is involved in a cycle

         For a suspended constraint on 'a to be in a cycle, a variable 
         in it's closure must be suspended and guards 'a. 

         The closure of this suspended constraint is 'c. 

         But 'c is locally bound to the let binding on `x`! 

         No other suspended constraint is associated with 'c. 

         Hence no cycle, contradiction!
         

       - <'a>([s] -> s <= 'c) ? mono is not involved in a cycle

         Then the cycle of suspended constraints must be contained in 
         [[ e' : 'b ]]. Recurse and contradict. 


     - e = e1 e2

       
       We have:

       [[ e : 't ]] =
         exists 'a 'b.
         [[ e1 : 'a ]] 
         && 'a = 'b -> 't 
         && let arg = \'c. [[ e2 : 'c ]] in
            <'b>([s] -> arg <= s) ? mono

       Two cases: 
       - <'b>([s] -> arg <= s) ? mono is not involved in a cycle
         
         Recursive and contradict in either e1 or e2. 

       - <'b>([s] -> arg <= s) ? mono is involved in a cycle.

         The closure of this constraint contains 'c.

         For a cycle, we need some variable reachable from 'c 
         with a suspended constraint (generated in [[ e2 : 'c ]]) 
         that transitively guards 'b.

         Key point: We ruled out above that `fun x -> e` can contribute to 
         a cycle. So suppose e2 contains an application, generating:

           exists 'd 'e.
           [[ e3 : 'd ]]
           && 'd = 'e -> 'l
           && let arg2 = \'f. [[ e4 : 'f ]] in
              <'e>([s] -> arg2 <= s) ? mono

         where 'l is a descendant of 'c. And 'e is a member of the 
         cycle involving 'b. Hence, it must also be the case that 'e 
         appears in 'l. 

         Key point: It is worth noting that 'l and 'e cannot be equal 
         (since 'l is a monotype variable and 'e is a polytype 
         variable). 

         Hence 'd must appear in 'l. But, this contradicts our 
         assumption for acyclic types (no equi-recursive types).

    So we are done.
*)

let%expect_test "" =
  (* rectypes can cause defaulting to fail for polyparams *)
  let str =
    {|
      let _ = fun f -> f f;;
    |}
  in
  type_check_and_print ~with_fcp:true str;
  [%expect {| |}]
;;

let%expect_test "polyparam schemes are distinct from first-class polymorphism" =
  let str =
    {|
      type 'a list = Nil | Cons of 'a * 'a list;;
      external id : 'a. 'a -> 'a;;
      external head : 'a. 'a list -> 'a;;
      external schemes : (forall 'a. 'a -> 'a) list;;
      external polys : ['a. 'a -> 'a] list;;
      external use_scheme : (forall 'a. 'a -> 'a) -> int;;
      external use_poly : ['a. 'a -> 'a] -> int;;

      let poly_id = [id];;
      let scheme_result = use_scheme (head schemes);;
      let poly_result = use_poly (head polys);;
      let explicit_poly_result = use_poly poly_id;;
    |}
  in
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external id : 'a -> 'a
    external head : 'b list -> 'b
    external schemes : (forall 'c. 'c -> 'c) list
    external polys : ['d. 'd -> 'd] list
    external use_scheme : (forall 'e. 'e -> 'e) -> int
    external use_poly : ['f. 'f -> 'f] -> int
    val poly_id : ['g. 'g -> 'g]
    val scheme_result : int
    val poly_result : int
    val explicit_poly_result : int
    |}]
;;

let%expect_test "a scheme is not an implicitly first-class polymorphic value" =
  let str =
    {|
      external id : 'a. 'a -> 'a;;
      external use_poly : ['a. 'a -> 'a] -> int;;
      let invalid_poly = use_poly id;;
    |}
  in
  type_check_and_print ~with_fcp:true str;
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:4:35
      4 │        let invalid_poly = use_poly id;;
        │                                    ^^ `'a -> 'a`
        │                                         is not equal to
        │                                       `['b. 'b -> 'b]`
    |}]
;;

let%expect_test "" =
  (* All examples from:
     - https://dl.acm.org/doi/pdf/10.1145/3408971 
     - https://dl.acm.org/doi/pdf/10.1145/3408971
     - https://arxiv.org/pdf/2607.16061
  *)
  let test =
    Incremental_test.create
      ~initial:
        (include_list
         ^ {|
              external head : 'a. 'a list -> 'a;;
              external tail : 'a. 'a list -> 'a list;;
              external nil : 'a. 'a list;;
              external cons : 'a. 'a -> 'a list -> 'a list;;
              external single : 'a. 'a -> 'a list;;
              external concat : 'a. 'a list -> 'a list -> 'a list;;
              external length : 'a. 'a list -> int;;
              external id : 'a. 'a -> 'a;;
              external inc : int -> int;;
              external choose : 'a. 'a -> 'a -> 'a;;
              external poly : (forall 'a. 'a -> 'a) -> int * bool;;
              external auto : (forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a);;
              external auto2 : 'b. (forall 'a. 'a -> 'a) -> 'b -> 'b;;
              external ids : (forall 'a. 'a -> 'a) list;;
              external map : 'a 'b. ('a -> 'b) -> 'a list -> 'b list;;
              external app : 'a 'b. ('a -> 'b) -> 'a -> 'b;;
              external revapp : 'a 'b. 'a -> ('a -> 'b) -> 'b;;
              external flip : 'a 'b 'c. ('a -> 'b -> 'c) -> 'b -> 'a -> 'c;;

              type ('s, 'a) st = 
                | St 
              ;;
              
              external run_st : 'v. (forall 's. ('s, 'v) st) -> 'v;;
              external arg_st : 's. ('s, int) st;;
              external compose : 'a 'b 'c. ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c;;
           |}
        )
      (type_check_and_print ~with_fcp:true)
  in
  [%expect
    {|
    type 'a list =
      | Nil
      | Cons of 'a * 'a list
    external head : 'a list -> 'a
    external tail : 'b list -> 'b list
    external nil : 'c list
    external cons : 'd -> 'd list -> 'd list
    external single : 'e -> 'e list
    external concat : 'f list -> 'f list -> 'f list
    external length : 'g list -> int
    external id : 'h -> 'h
    external inc : int -> int
    external choose : 'i -> 'i -> 'i
    external poly : (forall 'j. 'j -> 'j) -> int * bool
    external auto : (forall 'k. 'k -> 'k) -> (forall 'l. 'l -> 'l)
    external auto2 : (forall 'm. 'm -> 'm) -> 'n -> 'n
    external ids : (forall 'o. 'o -> 'o) list
    external map : ('p -> 'q) -> 'p list -> 'q list
    external app : ('r -> 's) -> 'r -> 's
    external revapp : 't -> ('t -> 'u) -> 'u
    external flip : ('v -> 'w -> 'x) -> 'w -> 'v -> 'x
    type ('s, 'a) st =
      | St
    external run_st : (forall 'z. ('z, 'y) st) -> 'y
    external arg_st : ('a1, int) st
    external compose : ('b1 -> 'c1) -> ('d1 -> 'b1) -> 'd1 -> 'c1
    |}];
  let do_test = Incremental_test.run test in
  (* A1 *)
  do_test
    {|
      let const2 = fun x y -> y;;
    |};
  [%expect {| val const2 : 'e1 -> 'f1 -> 'f1 |}];
  (* A2 *)
  do_test
    {|
      let a2 = choose id;;
    |};
  [%expect {| val a2 : ('e1 -> 'e1) -> 'e1 -> 'e1 |}];
  (* A3: infers [(forall 'a. 'a -> 'a) list]. *)
  do_test
    {|
      let a3 = choose nil ids;;
    |};
  [%expect {| val a3 : (forall 'e1. 'e1 -> 'e1) list |}];
  (* A4 *)
  do_test
    {|
      let a4 = fun (forall x : 'a. 'a -> 'a) -> x x;;
    |};
  [%expect {| val a4 : (forall 'e1. 'e1 -> 'e1) -> 'f1 -> 'f1 |}];
  (* A5 *)
  do_test
    {|
      let a5 = id auto;;
    |};
  [%expect {| val a5 : (forall 'e1. 'e1 -> 'e1) -> (forall 'f1. 'f1 -> 'f1) |}];
  (* A6 *)
  do_test
    {|
      let a6 = id auto2;;
    |};
  [%expect {| val a6 : (forall 'e1. 'e1 -> 'e1) -> 'f1 -> 'f1 |}];
  (* A7 *)
  do_test
    {|
      let a7 = choose id auto;;
    |};
  [%expect {| val a7 : (forall 'e1. 'e1 -> 'e1) -> (forall 'f1. 'f1 -> 'f1) |}];
  (* A8 (Fresco X, QL X, HMF X, MLF +, ATIA X, FCIF X) *)
  do_test
    {|
      let a8 = choose id auto2;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:34:23
     34 │        let a8 = choose id auto2;;
        │                        ^^ `'a -> 'a`
        │                             is not equal to
        │                           `(forall 'b. 'b -> 'b) -> 'c -> 'c`
    |}];
  (* A9 *)
  do_test
    {|
      external f : 'a. ('a -> 'a) -> 'a list -> 'a;;
      let a9 = f (choose id) ids;;
    |};
  [%expect
    {|
    external f : ('e1 -> 'e1) -> 'e1 list -> 'e1
    val a9 : 'f1 -> 'f1
    |}];
  (* A10a *)
  do_test
    {|
      let a10a = poly id;;
    |};
  [%expect {| val a10a : int * bool |}];
  (* A10b *)
  do_test
    {|
      let a10b = poly (fun x -> x);;
    |};
  [%expect {| val a10b : int * bool |}];
  (* A10c *)
  do_test
    {|
      let a10c = id poly (fun x -> x);;
    |};
  [%expect {| val a10c : int * bool |}];
  (* A11 *)
  do_test
    {|
      external k : 'a. 'a -> 'a list -> int;;
      external xs : ((forall 'a. 'a -> 'a) -> int * bool) list;;
      let a11 = k (fun f -> (f 42, f true)) xs;;
    |};
  [%expect
    {|
    external k : 'e1 -> 'e1 list -> int
    external xs : ((forall 'f1. 'f1 -> 'f1) -> int * bool) list
    val a11 : int
    |}];
  (* A12a (called D1 in GI) *)
  do_test
    {|
      let a12a = app poly id;;
    |};
  [%expect {| val a12a : int * bool |}];
  (* A12b (called D2 in GI) *)
  do_test
    {|
      let a12b = revapp id poly;;
    |};
  [%expect {| val a12b : int * bool |}];
  (* A13z (called D3 in GI) *)
  do_test
    {|
      let a13z = run_st arg_st;;
    |};
  [%expect {| val a13z : int |}];
  (* A13a (called D4 in GI) *)
  do_test
    {|
      let a13a = app run_st arg_st;;
    |};
  [%expect {| val a13a : int |}];
  (* A13b (called D5 in GI) *)
  do_test
    {|
      let a13b = revapp arg_st run_st;;
    |};
  [%expect {| val a13b : int |}];
  (* C1 in GI *)
  do_test
    {|
      let b1z = length ids;;
    |};
  [%expect {| val b1z : int |}];
  (* B1a (called C2 in GI) *)
  do_test
    {|
      let b1a = tail ids;;
    |};
  [%expect {| val b1a : (forall 'e1. 'e1 -> 'e1) list |}];
  (* B1b (called C3 in GI) *)
  do_test
    {|
      let b1b = head ids;;
    |};
  [%expect {| val b1b : 'e1 -> 'e1 |}];
  (* B1c (called C4 in GI) *)
  do_test
    {|
      let b1c = single id;;
    |};
  [%expect {| val b1c : ('e1 -> 'e1) list |}];
  (* B2 (called C5 in GI) *)
  do_test
    {|
      let b2 = cons id ids;;
    |};
  [%expect {| val b2 : (forall 'e1. 'e1 -> 'e1) list |}];
  (* B3 (called C6 in GI) *)
  do_test
    {|
      let b3 = cons (fun x -> x) ids;;
    |};
  [%expect {| val b3 : (forall 'e1. 'e1 -> 'e1) list |}];
  (* B4 (called C7 in GI) *)
  do_test
    {|
      let b4 = concat (single inc) (single id);;
    |};
  [%expect {| val b4 : (int -> int) list |}];
  (* B5 (replaces C8 in GI) *)
  do_test
    {|
      let b5 = concat (single id) ids;;
    |};
  [%expect {| val b5 : (forall 'e1. 'e1 -> 'e1) list |}];
  (* B6 (called C9 in GI) *)
  do_test
    {|
      let b6 = map poly (single id);;
    |};
  [%expect {| val b6 : (int * bool) list |}];
  (* B7 (Fresco X, QL +, GI +, called C10 in GI) *)
  do_test
    {|
      let b7 = map head (single ids);;
    |};
  [%expect {| val b7 : (forall 'e1. 'e1 -> 'e1) list |}];
  (* B8 *)
  do_test
    {|
      let b8 = head ids true;;
    |};
  [%expect {| val b8 : bool |}];
  (* C1a (everyone fails on this, called B1 in GI) *)
  do_test
    {|
      let c1a = fun f -> (f 1, f true);;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:34:34
     34 │        let c1a = fun f -> (f 1, f true);;
        │                                   ^^^^ `bool`
        │                                          is not equal to
        │                                        `int`
    |}];
  (* C1b *)
  do_test
    {|
      let c1b = fun (forall f : 'a. 'a -> 'a) -> (f 1, f true);;
    |};
  [%expect {| val c1b : (forall 'e1. 'e1 -> 'e1) -> int * bool |}];
  (* C1c (MLF X, GI X, QL +, Fresco +) *)
  do_test
    {|
      external g : ((forall 'a. 'a -> 'a) -> int * bool) -> unit;;
      let c1c = g (fun f -> (f 42, f true));;
    |};
  [%expect
    {|
    external g : ((forall 'e1. 'e1 -> 'e1) -> int * bool) -> unit
    val c1c : unit
    |}];
  (* C2 (called E3 in GI) *)
  do_test
    {|
      external r : (forall 'a. 'a -> (forall 'b. 'b -> 'b)) -> int;;
      let c2 = r (fun x y -> y);;
    |};
  [%expect
    {|
    external r : (forall 'f1. 'f1 -> (forall 'e1. 'e1 -> 'e1)) -> int
    val c2 : int
    |}];
  (* eta-expansion dependencies *)
  do_test
    ~add:true
    {|
      external h : int -> (forall 'a. 'a -> 'a);;
      external k : 'a. 'a -> 'a list -> 'a;;
      external lst : (forall 'a. int -> 'a -> 'a) list;;
    |};
  [%expect
    {|
    external h : int -> (forall 'e1. 'e1 -> 'e1)
    external k : 'f1 -> 'f1 list -> 'f1
    external lst : (forall 'g1. int -> 'g1 -> 'g1) list
    |}];
  (* E1a (everyone fails on this) *)
  do_test
    {|
      let e1a = k h lst;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:38:19
     38 │        let e1a = k h lst;;
        │                    ^ `int -> (forall 'a. 'a -> 'a)`
        │                        is not equal to
        │                      `int -> 'b -> 'b`
    |}];
  (* E1b (called E2 in GI) *)
  do_test
    {|
      let e1b = k (fun x -> h x) lst;;
    |};
  [%expect {| val e1b : int -> 'h1 -> 'h1 |}];
  (* E2a (MLF +) *)
  do_test
    {|
      let e2a = fun x -> poly x;;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:38:31
     38 │        let e2a = fun x -> poly x;;
        │                                ^
    |}];
  (* E2b *)
  do_test
    {|
      let e2b = (fun x -> poly x : (forall 'a. 'a -> 'a) -> int * bool);;
     |};
  [%expect {| val e2b : (forall 'h1. 'h1 -> 'h1) -> int * bool |}];
  (* E3a *)
  do_test
    {|
      let e3a = app poly id;;
    |};
  [%expect {| val e3a : int * bool |}];
  (* E3b (Fresco passes with freezing) *)
  do_test
    {|
      let e3b = app (fun x -> poly x) id;;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:38:36
     38 │        let e3b = app (fun x -> poly x) id;;
        │                                     ^
    |}];
  (* E4a *)
  do_test
    {|
      let e4a = map poly ids;; 
    |};
  [%expect {| val e4a : (int * bool) list |}];
  (* E4b *)
  do_test
    {|
      let e4b = map (fun x -> x) ids;;
    |};
  [%expect {| val e4b : ('h1 -> 'h1) list |}];
  (* E5a (Fresco fails) *)
  do_test
    {|
      let e5a = compose poly head;;
    |};
  [%expect {| val e5a : (forall 'h1. 'h1 -> 'h1) list -> int * bool |}];
  (* E5b (called B2 in GI) *)
  do_test
    {|
      let b2 = fun xs -> poly (head xs);;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:38:32
     38 │        let b2 = fun xs -> poly (head xs);;
        │                                 ^^^^^^^
    |}];
  (* E6 *)
  do_test
    {|
      let e6 = (fun f -> app f) poly id;;
    |};
  [%expect {| val e6 : int * bool |}];
  (* E7 (Fresco fails without freezing) *)
  do_test
    {|
      let e7 = (fun f -> app poly f) id;;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:38:35
     38 │        let e7 = (fun f -> app poly f) id;;
        │                                    ^
    |}];
  (* F1 *)
  do_test
    {|
      let f1 = map (fun f -> (f true, f 42)) ids;;
    |};
  [%expect {| val f1 : (bool * int) list |}];
  (* F2 (Fresco fails without freezing) *)
  do_test
    {|
      let f2 = app (fun f -> (f true, f 42)) id;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:38:41
     38 │        let f2 = app (fun f -> (f true, f 42)) id;;
        │                                          ^^ `int`
        │                                               is not equal to
        │                                             `bool`
    |}];
  (* F3 (Fresco X, QL +) *)
  do_test
    {|
      let f3 = map id ids;;
    |};
  [%expect {| val f3 : (forall 'h1. 'h1 -> 'h1) list |}];
  (* F4 (Fresco fails without freezing) *)
  do_test
    {|
      let f4 = (fun f -> (f 42, f true)) id;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:38:35
     38 │        let f4 = (fun f -> (f 42, f true)) id;;
        │                                    ^^^^ `bool`
        │                                           is not equal to
        │                                         `int`
    |}];
  (* F5 *)
  do_test
    {|
      external pair : 'a 'b. 'a -> 'b -> 'a * 'b;;
      let f5 = (pair (fun x -> 42) 42 : ((forall 'a. 'a -> 'a) -> int) * int);;
    |};
  [%expect
    {|
    external pair : 'h1 -> 'i1 -> 'h1 * 'i1
    val f5 : ((forall 'j1. 'j1 -> 'j1) -> int) * int
    |}];
  (* F6 *)
  do_test
    {|
      let f6 = choose nil ids;;
    |};
  [%expect {| val f6 : (forall 'h1. 'h1 -> 'h1) list |}];
  (* F7 *)
  do_test
    {|
      let f7 = head (choose nil ids);;
    |};
  [%expect {| val f7 : 'h1 -> 'h1 |}];
  (* F8 (QL X, Fresco +) *)
  do_test
    {|
      external f : 'a. (int -> 'a) -> 'a;;
      let f8 = f (fun x -> ids);;
    |};
  [%expect
    {|
    external f : (int -> 'h1) -> 'h1
    val f8 : (forall 'i1. 'i1 -> 'i1) list
    |}];
  (* F9 (QL X, Fresco +) *)
  do_test
    {|
      external f : 'a. (forall 'b. 'b -> 'b * 'a) -> 'a;;      
      let f9 = f (fun x -> (x, ids));;
    |};
  [%expect
    {|
    external f : (forall 'i1. 'i1 -> 'i1 * 'h1) -> 'h1
    val f9 : (forall 'j1. 'j1 -> 'j1) list
    |}];
  (* F10 (QL X, Fresco +) *)
  do_test
    {|
      external f : 'a. ((forall 'b. 'b -> 'b) -> 'a) -> 'a;;      
      let f10 = f (fun x -> ids);;
    |};
  [%expect
    {|
    external f : ((forall 'h1. 'h1 -> 'h1) -> 'i1) -> 'i1
    val f10 : (forall 'j1. 'j1 -> 'j1) list
    |}];
  (* F11a *)
  do_test
    {|
      external polys : (forall 'a. 'a -> 'a) list -> int * bool;;
      let f11a = polys (single id);;      
    |};
  [%expect
    {|
    external polys : (forall 'h1. 'h1 -> 'h1) list -> int * bool
    val f11a : int * bool
    |}];
  (* F11b (Fresco fails without freezing, QL X) *)
  do_test
    {|
      external polys : (forall 'a. 'a -> 'a) list -> int * bool;;
      let f11b = let xs = single id in polys xs;;      
    |};
  [%expect
    {|
    external polys : (forall 'h1. 'h1 -> 'h1) list -> int * bool
    val f11b : int * bool
    |}];
  (* F12 (From p10 in Fresco) *)
  do_test
    {|
      external g : 'b. (forall 'a. 'a -> 'a) -> 'b -> 'b list;;
      external f : 'c 'd. ('c -> 'c -> 'd list) -> int;;
      let f12 = f g;;
    |};
  [%expect
    {|
    external g : (forall 'h1. 'h1 -> 'h1) -> 'i1 -> 'i1 list
    external f : ('j1 -> 'j1 -> 'k1 list) -> int
    val f12 : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type ('a, 'b) mapping = 'a -> 'b;;
      external apply : 'a 'b. ('a, 'b) mapping -> 'a -> 'b;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type ('a, 'b) mapping =
      'a -> 'b
    external apply : ('a -> 'b) -> 'a -> 'b
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type 'a pair = 'a * 'a;;
      type int_pair = int pair;;
      type box = Box of int_pair;;
      let boxed = Box (1, 2);;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    type 'a pair =
      'a * 'a
    type int_pair =
      int pair
    type box =
      | Box of int_pair
    val boxed : box
    |}]
;;

let%expect_test "" =
  let str =
    {|
      type ('a, 'b) pair = 'a * 'b;;
      external bad : 'a. 'a pair;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E008]: type takes 2 arguments but 1 arguments were supplied
        ┌─ expect_test.ml:3:29
      3 │        external bad : 'a. 'a pair;;
        │                           -- ^^^^ expected 2 arguments
        │                           │
        │                           supplied 1 arguments
    |}]
;;

let%expect_test "church-encoded lists for FCP" =
  (* All examples from:
     - https://dl.acm.org/doi/pdf/10.1145/3408971 
     - https://dl.acm.org/doi/pdf/10.1145/3408971
     - https://arxiv.org/pdf/2607.16061
  *)
  let test =
    Incremental_test.create
      ~initial:
        {|
          type 'a list = (forall 'b. 'b -> ('a -> 'b -> 'b) -> 'b);;
          
          external head : 'a. 'a list -> 'a;;
          external tail : 'a. 'a list -> 'a list;;
          external nil : 'a. 'a list;;
          external cons : 'a. 'a -> 'a list -> 'a list;;
          external single : 'a. 'a -> 'a list;;
          external concat : 'a. 'a list -> 'a list -> 'a list;;
          external length : 'a. 'a list -> int;;
          external id : 'a. 'a -> 'a;;
          external inc : int -> int;;
          external choose : 'a. 'a -> 'a -> 'a;;
          external poly : (forall 'a. 'a -> 'a) -> int * bool;;
          external auto : (forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a);;
          external auto2 : 'b. (forall 'a. 'a -> 'a) -> 'b -> 'b;;
          external ids : (forall 'a. 'a -> 'a) list;;
          external map : 'a 'b. ('a -> 'b) -> 'a list -> 'b list;;
          external app : 'a 'b. ('a -> 'b) -> 'a -> 'b;;
          external revapp : 'a 'b. 'a -> ('a -> 'b) -> 'b;;
          external flip : 'a 'b 'c. ('a -> 'b -> 'c) -> 'b -> 'a -> 'c;;

          type ('s, 'a) st = 
            | St 
          ;;
          
          external run_st : 'v. (forall 's. ('s, 'v) st) -> 'v;;
          external arg_st : 's. ('s, int) st;;
          external compose : 'a 'b 'c. ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c;;
         |}
      (type_check_and_print ~with_fcp:true)
  in
  [%expect
    {|
    type 'a list =
      (forall 'b. 'b -> ('a -> 'b -> 'b) -> 'b)
    external head : (forall 'b. 'b -> ('a -> 'b -> 'b) -> 'b) -> 'a
    external tail :
      (forall 'd. 'd -> ('c -> 'd -> 'd) -> 'd) ->
      (forall 'e. 'e -> ('c -> 'e -> 'e) -> 'e)
    external nil : 'f -> ('g -> 'f -> 'f) -> 'f
    external cons :
      'h ->
      (forall 'i. 'i -> ('h -> 'i -> 'i) -> 'i) ->
      (forall 'j. 'j -> ('h -> 'j -> 'j) -> 'j)
    external single : 'k -> (forall 'l. 'l -> ('k -> 'l -> 'l) -> 'l)
    external concat :
      (forall 'n. 'n -> ('m -> 'n -> 'n) -> 'n) ->
      (forall 'o. 'o -> ('m -> 'o -> 'o) -> 'o) ->
      (forall 'p. 'p -> ('m -> 'p -> 'p) -> 'p)
    external length : (forall 'r. 'r -> ('q -> 'r -> 'r) -> 'r) -> int
    external id : 's -> 's
    external inc : int -> int
    external choose : 't -> 't -> 't
    external poly : (forall 'u. 'u -> 'u) -> int * bool
    external auto : (forall 'v. 'v -> 'v) -> (forall 'w. 'w -> 'w)
    external auto2 : (forall 'x. 'x -> 'x) -> 'y -> 'y
    external ids : 'z -> ((forall 'a1. 'a1 -> 'a1) -> 'z -> 'z) -> 'z
    external map :
      ('b1 -> 'c1) ->
      (forall 'd1. 'd1 -> ('b1 -> 'd1 -> 'd1) -> 'd1) ->
      (forall 'e1. 'e1 -> ('c1 -> 'e1 -> 'e1) -> 'e1)
    external app : ('f1 -> 'g1) -> 'f1 -> 'g1
    external revapp : 'h1 -> ('h1 -> 'i1) -> 'i1
    external flip : ('j1 -> 'k1 -> 'l1) -> 'k1 -> 'j1 -> 'l1
    type ('s, 'a) st =
      | St
    external run_st : (forall 'n1. ('n1, 'm1) st) -> 'm1
    external arg_st : ('o1, int) st
    external compose : ('p1 -> 'q1) -> ('r1 -> 'p1) -> 'r1 -> 'q1
    |}];
  let do_test = Incremental_test.run test in
  (* A1 *)
  do_test
    {|
      let const2 = fun x y -> y;;
    |};
  [%expect {| val const2 : 's1 -> 't1 -> 't1 |}];
  (* A2 *)
  do_test
    {|
      let a2 = choose id;;
    |};
  [%expect {| val a2 : ('s1 -> 's1) -> 's1 -> 's1 |}];
  (* A3: infers [(forall 'a. 'a -> 'a) list]. *)
  do_test
    {|
      let a3 = choose nil ids;;
    |};
  [%expect {| val a3 : 's1 -> ((forall 't1. 't1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* A4 *)
  do_test
    {|
      let a4 = fun (forall x : 'a. 'a -> 'a) -> x x;;
    |};
  [%expect {| val a4 : (forall 's1. 's1 -> 's1) -> 't1 -> 't1 |}];
  (* A5 *)
  do_test
    {|
      let a5 = id auto;;
    |};
  [%expect {| val a5 : (forall 's1. 's1 -> 's1) -> (forall 't1. 't1 -> 't1) |}];
  (* A6 *)
  do_test
    {|
      let a6 = id auto2;;
    |};
  [%expect {| val a6 : (forall 's1. 's1 -> 's1) -> 't1 -> 't1 |}];
  (* A7 *)
  do_test
    {|
      let a7 = choose id auto;;
    |};
  [%expect {| val a7 : (forall 's1. 's1 -> 's1) -> (forall 't1. 't1 -> 't1) |}];
  (* A8 (Fresco X, QL X, HMF X, MLF +, ATIA X, FCIF X) *)
  do_test
    {|
      let a8 = choose id auto2;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:31:23
     31 │        let a8 = choose id auto2;;
        │                        ^^ `'a -> 'a`
        │                             is not equal to
        │                           `(forall 'b. 'b -> 'b) -> 'c -> 'c`
    |}];
  (* A9 *)
  do_test
    {|
      external f : 'a. ('a -> 'a) -> 'a list -> 'a;;
      let a9 = f (choose id) ids;;
    |};
  [%expect
    {|
    external f :
      ('s1 -> 's1) -> (forall 't1. 't1 -> ('s1 -> 't1 -> 't1) -> 't1) -> 's1
    val a9 : 'u1 -> 'u1
    |}];
  (* A10a *)
  do_test
    {|
      let a10a = poly id;;
    |};
  [%expect {| val a10a : int * bool |}];
  (* A10b *)
  do_test
    {|
      let a10b = poly (fun x -> x);;
    |};
  [%expect {| val a10b : int * bool |}];
  (* A10c *)
  do_test
    {|
      let a10c = id poly (fun x -> x);;
    |};
  [%expect {| val a10c : int * bool |}];
  (* A11 *)
  do_test
    {|
      external k : 'a. 'a -> 'a list -> int;;
      external xs : ((forall 'a. 'a -> 'a) -> int * bool) list;;
      let a11 = k (fun f -> (f 42, f true)) xs;;
    |};
  [%expect
    {|
    external k : 's1 -> (forall 't1. 't1 -> ('s1 -> 't1 -> 't1) -> 't1) -> int
    external xs :
      'u1 -> (((forall 'v1. 'v1 -> 'v1) -> int * bool) -> 'u1 -> 'u1) -> 'u1
    val a11 : int
    |}];
  (* A12a (called D1 in GI) *)
  do_test
    {|
      let a12a = app poly id;;
    |};
  [%expect {| val a12a : int * bool |}];
  (* A12b (called D2 in GI) *)
  do_test
    {|
      let a12b = revapp id poly;;
    |};
  [%expect {| val a12b : int * bool |}];
  (* A13z (called D3 in GI) *)
  do_test
    {|
      let a13z = run_st arg_st;;
    |};
  [%expect {| val a13z : int |}];
  (* A13a (called D4 in GI) *)
  do_test
    {|
      let a13a = app run_st arg_st;;
    |};
  [%expect {| val a13a : int |}];
  (* A13b (called D5 in GI) *)
  do_test
    {|
      let a13b = revapp arg_st run_st;;
    |};
  [%expect {| val a13b : int |}];
  (* C1 in GI *)
  do_test
    {|
      let b1z = length ids;;
    |};
  [%expect {| val b1z : int |}];
  (* B1a (called C2 in GI) *)
  do_test
    {|
      let b1a = tail ids;;
    |};
  [%expect {| val b1a : 's1 -> ((forall 't1. 't1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* B1b (called C3 in GI) *)
  do_test
    {|
      let b1b = head ids;;
    |};
  [%expect {| val b1b : 's1 -> 's1 |}];
  (* B1c (called C4 in GI) *)
  do_test
    {|
      let b1c = single id;;
    |};
  [%expect {| val b1c : 's1 -> (('t1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* B2 (called C5 in GI) *)
  do_test
    {|
      let b2 = cons id ids;;
    |};
  [%expect {| val b2 : 's1 -> ((forall 't1. 't1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* B3 (called C6 in GI) *)
  do_test
    {|
      let b3 = cons (fun x -> x) ids;;
    |};
  [%expect {| val b3 : 's1 -> ((forall 't1. 't1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* B4 (called C7 in GI) *)
  do_test
    {|
      let b4 = concat (single inc) (single id);;
    |};
  [%expect {| val b4 : 's1 -> ((int -> int) -> 's1 -> 's1) -> 's1 |}];
  (* B5 (replaces C8 in GI) *)
  do_test
    {|
      let b5 = concat (single id) ids;;
    |};
  [%expect {| val b5 : 's1 -> ((forall 't1. 't1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* B6 (called C9 in GI) *)
  do_test
    {|
      let b6 = map poly (single id);;
    |};
  [%expect {| val b6 : 's1 -> (int * bool -> 's1 -> 's1) -> 's1 |}];
  (* B7 (Fresco X, QL +, GI +, called C10 in GI) *)
  do_test
    {|
      let b7 = map head (single ids);;
    |};
  [%expect {| val b7 : 's1 -> ((forall 't1. 't1 -> 't1) -> 's1 -> 's1) -> 's1 |}];
  (* B8 *)
  do_test
    {|
      let b8 = head ids true;;
    |};
  [%expect {| val b8 : bool |}];
  (* C1a (everyone fails on this, called B1 in GI) *)
  do_test
    {|
      let c1a = fun f -> (f 1, f true);;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:31:34
     31 │        let c1a = fun f -> (f 1, f true);;
        │                                   ^^^^ `bool`
        │                                          is not equal to
        │                                        `int`
    |}];
  (* C1b *)
  do_test
    {|
      let c1b = fun (forall f : 'a. 'a -> 'a) -> (f 1, f true);;
    |};
  [%expect {| val c1b : (forall 's1. 's1 -> 's1) -> int * bool |}];
  (* C1c (MLF X, GI X, QL +, Fresco +) *)
  do_test
    {|
      external g : ((forall 'a. 'a -> 'a) -> int * bool) -> unit;;
      let c1c = g (fun f -> (f 42, f true));;
    |};
  [%expect
    {|
    external g : ((forall 's1. 's1 -> 's1) -> int * bool) -> unit
    val c1c : unit
    |}];
  (* C2 (called E3 in GI) *)
  do_test
    {|
      external r : (forall 'a. 'a -> (forall 'b. 'b -> 'b)) -> int;;
      let c2 = r (fun x y -> y);;
    |};
  [%expect
    {|
    external r : (forall 't1. 't1 -> (forall 's1. 's1 -> 's1)) -> int
    val c2 : int
    |}];
  (* eta-expansion dependencies *)
  do_test
    ~add:true
    {|
      external h : int -> (forall 'a. 'a -> 'a);;
      external k : 'a. 'a -> 'a list -> 'a;;
      external lst : (forall 'a. int -> 'a -> 'a) list;;
    |};
  [%expect
    {|
    external h : int -> (forall 's1. 's1 -> 's1)
    external k : 't1 -> (forall 'u1. 'u1 -> ('t1 -> 'u1 -> 'u1) -> 'u1) -> 't1
    external lst : 'v1 -> ((forall 'w1. int -> 'w1 -> 'w1) -> 'v1 -> 'v1) -> 'v1
    |}];
  (* E1a (everyone fails on this) *)
  do_test
    {|
      let e1a = k h lst;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:35:19
     35 │        let e1a = k h lst;;
        │                    ^ `int -> (forall 'a. 'a -> 'a)`
        │                        is not equal to
        │                      `int -> 'b -> 'b`
    |}];
  (* E1b (called E2 in GI) *)
  do_test
    {|
      let e1b = k (fun x -> h x) lst;;
    |};
  [%expect {| val e1b : int -> 'x1 -> 'x1 |}];
  (* E2a (MLF +) *)
  do_test
    {|
      let e2a = fun x -> poly x;;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:35:31
     35 │        let e2a = fun x -> poly x;;
        │                                ^
    |}];
  (* E2b *)
  do_test
    {|
      let e2b = (fun x -> poly x : (forall 'a. 'a -> 'a) -> int * bool);;
     |};
  [%expect {| val e2b : (forall 'x1. 'x1 -> 'x1) -> int * bool |}];
  (* E3a *)
  do_test
    {|
      let e3a = app poly id;;
    |};
  [%expect {| val e3a : int * bool |}];
  (* E3b (Fresco passes with freezing) *)
  do_test
    {|
      let e3b = app (fun x -> poly x) id;;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:35:36
     35 │        let e3b = app (fun x -> poly x) id;;
        │                                     ^
    |}];
  (* E4a *)
  do_test
    {|
      let e4a = map poly ids;; 
    |};
  [%expect {| val e4a : 'x1 -> (int * bool -> 'x1 -> 'x1) -> 'x1 |}];
  (* E4b *)
  do_test
    {|
      let e4b = map (fun x -> x) ids;;
    |};
  [%expect {| val e4b : 'x1 -> (('y1 -> 'y1) -> 'x1 -> 'x1) -> 'x1 |}];
  (* E5a (Fresco fails) *)
  do_test
    {|
      let e5a = compose poly head;;
    |};
  [%expect
    {|
    val e5a :
      (forall 'y1. 'y1 -> ((forall 'x1. 'x1 -> 'x1) -> 'y1 -> 'y1) -> 'y1) ->
      int * bool
    |}];
  (* E5b (called B2 in GI) *)
  do_test
    {|
      let b2 = fun xs -> poly (head xs);;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:35:37
     35 │        let b2 = fun xs -> poly (head xs);;
        │                                      ^^
    |}];
  (* E6 *)
  do_test
    {|
      let e6 = (fun f -> app f) poly id;;
    |};
  [%expect {| val e6 : int * bool |}];
  (* E7 (Fresco fails without freezing) *)
  do_test
    {|
      let e7 = (fun f -> app poly f) id;;
    |};
  [%expect
    {|
    error[E012]: generic type variable escapes its scope
        ┌─ expect_test.ml:35:35
     35 │        let e7 = (fun f -> app poly f) id;;
        │                                    ^
    |}];
  (* F1 *)
  do_test
    {|
      let f1 = map (fun f -> (f true, f 42)) ids;;
    |};
  [%expect {| val f1 : 'x1 -> (bool * int -> 'x1 -> 'x1) -> 'x1 |}];
  (* F2 (Fresco fails without freezing) *)
  do_test
    {|
      let f2 = app (fun f -> (f true, f 42)) id;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:35:41
     35 │        let f2 = app (fun f -> (f true, f 42)) id;;
        │                                          ^^ `int`
        │                                               is not equal to
        │                                             `bool`
    |}];
  (* F3 (Fresco X, QL +) *)
  do_test
    {|
      let f3 = map id ids;;
    |};
  [%expect {| val f3 : 'x1 -> ((forall 'y1. 'y1 -> 'y1) -> 'x1 -> 'x1) -> 'x1 |}];
  (* F4 (Fresco fails without freezing) *)
  do_test
    {|
      let f4 = (fun f -> (f 42, f true)) id;;
    |};
  [%expect
    {|
    error[E011]: mismatched type
        ┌─ expect_test.ml:35:35
     35 │        let f4 = (fun f -> (f 42, f true)) id;;
        │                                    ^^^^ `bool`
        │                                           is not equal to
        │                                         `int`
    |}];
  (* F5 *)
  do_test
    {|
      external pair : 'a 'b. 'a -> 'b -> 'a * 'b;;
      let f5 = (pair (fun x -> 42) 42 : ((forall 'a. 'a -> 'a) -> int) * int);;
    |};
  [%expect
    {|
    external pair : 'x1 -> 'y1 -> 'x1 * 'y1
    val f5 : ((forall 'z1. 'z1 -> 'z1) -> int) * int
    |}];
  (* F6 *)
  do_test
    {|
      let f6 = choose nil ids;;
    |};
  [%expect {| val f6 : 'x1 -> ((forall 'y1. 'y1 -> 'y1) -> 'x1 -> 'x1) -> 'x1 |}];
  (* F7 *)
  do_test
    {|
      let f7 = head (choose nil ids);;
    |};
  [%expect {| val f7 : 'x1 -> 'x1 |}];
  (* F8 (QL X, Fresco +) *)
  do_test
    {|
      external f : 'a. (int -> 'a) -> 'a;;
      let f8 = f (fun x -> ids);;
    |};
  [%expect
    {|
    external f : (int -> 'x1) -> 'x1
    val f8 : 'y1 -> ((forall 'z1. 'z1 -> 'z1) -> 'y1 -> 'y1) -> 'y1
    |}];
  (* F9 (QL X, Fresco +) *)
  do_test
    {|
      external f : 'a. (forall 'b. 'b -> 'b * 'a) -> 'a;;      
      let f9 = f (fun x -> (x, ids));;
    |};
  [%expect
    {|
    external f : (forall 'y1. 'y1 -> 'y1 * 'x1) -> 'x1
    val f9 : 'z1 -> ((forall 'a2. 'a2 -> 'a2) -> 'z1 -> 'z1) -> 'z1
    |}];
  (* F10 (QL X, Fresco +) *)
  do_test
    {|
      external f : 'a. ((forall 'b. 'b -> 'b) -> 'a) -> 'a;;      
      let f10 = f (fun x -> ids);;
    |};
  [%expect
    {|
    external f : ((forall 'x1. 'x1 -> 'x1) -> 'y1) -> 'y1
    val f10 : 'z1 -> ((forall 'a2. 'a2 -> 'a2) -> 'z1 -> 'z1) -> 'z1
    |}];
  (* F11a *)
  do_test
    {|
      external polys : (forall 'a. 'a -> 'a) list -> int * bool;;
      let f11a = polys (single id);;      
    |};
  [%expect
    {|
    external polys :
      (forall 'y1. 'y1 -> ((forall 'x1. 'x1 -> 'x1) -> 'y1 -> 'y1) -> 'y1) ->
      int * bool
    val f11a : int * bool
    |}];
  (* F11b (Fresco fails without freezing, QL X) *)
  do_test
    {|
      external polys : (forall 'a. 'a -> 'a) list -> int * bool;;
      let f11b = let xs = single id in polys xs;;      
    |};
  [%expect
    {|
    external polys :
      (forall 'y1. 'y1 -> ((forall 'x1. 'x1 -> 'x1) -> 'y1 -> 'y1) -> 'y1) ->
      int * bool
    val f11b : int * bool
    |}];
  (* F12 (From p10 in Fresco) *)
  do_test
    {|
      external g : 'b. (forall 'a. 'a -> 'a) -> 'b -> 'b list;;
      external f : 'c 'd. ('c -> 'c -> 'd list) -> int;;
      let f12 = f g;;
    |};
  [%expect
    {|
    external g :
      (forall 'x1. 'x1 -> 'x1) ->
      'y1 -> (forall 'z1. 'z1 -> ('y1 -> 'z1 -> 'z1) -> 'z1)
    external f :
      ('a2 -> 'a2 -> (forall 'c2. 'c2 -> ('b2 -> 'c2 -> 'c2) -> 'c2)) -> int
    val f12 : int
    |}]
;;

let%expect_test "" =
  let str =
    {|
      let non_linear_pattern = fun (x, x) -> x;;
    |}
  in
  type_check_and_print str;
  [%expect
    {|
    error[E019]: identifier `x` is bound more than once in the same pattern
        ┌─ expect_test.ml:2:40
      2 │        let non_linear_pattern = fun (x, x) -> x;;
        │                                      -  ^ bound here again
        │                                      │
        │                                      bound here
        = hint: if this is intentional, prefix it with an underscore `_x`
    |}]
;;

let%expect_test "" =
  type_check_and_print
    {|
      type poly = Poly of (forall 'a. 'a -> 'a);;
    |};
  [%expect
    {|
    error[E020]: first-class polymorphism is disabled
        ┌─ expect_test.ml:2:27
      2 │        type poly = Poly of (forall 'a. 'a -> 'a);;
        │                            ^^^^^^^^^^^^^^^^^^^^^ requires first-class polymorphism
        = hint: enable this feature with `-ffcp`
    |}];
  type_check_and_print
    {|
      external use_poly : (forall 'a. 'a -> 'a) -> int;;
    |};
  [%expect
    {|
    error[E020]: first-class polymorphism is disabled
        ┌─ expect_test.ml:2:27
      2 │        external use_poly : (forall 'a. 'a -> 'a) -> int;;
        │                            ^^^^^^^^^^^^^^^^^^^^^ requires first-class polymorphism
        = hint: enable this feature with `-ffcp`
    |}];
  type_check_and_print
    {|
      let use_poly = fun (forall id : 'a. 'a -> 'a) -> id 0;;
    |};
  [%expect
    {|
    error[E020]: first-class polymorphism is disabled
        ┌─ expect_test.ml:2:26
      2 │        let use_poly = fun (forall id : 'a. 'a -> 'a) -> id 0;;
        │                           ^^^^^^^^^^^^^^^^^^^^^^^^^^ requires first-class polymorphism
        = hint: enable this feature with `-ffcp`
    |}]
;;
