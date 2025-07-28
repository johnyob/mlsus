open Core
open Mlsus_std
open Grace

module rec Type : sig
  module Ident : Var.S
  module Var : Var.S

  (** [t] represents the type [tau]. *)
  type t =
    | Var of Var.t (** Type variable ['a] *)
    | Arrow of t * t (** Function types [tua1 -> tau2] *)
    | Tuple of t list (** Tuple types [tau1 * ... * taun] *)
    | Constr of t list * Ident.t (** Nominal types [(tau1, ..., taun) T] *)
    | Shape of t list * Principal_shape.t (** Applied shape [(tau1, ..., taun) s] *)
    | Poly of Type_scheme.t (** Polytypes [[sigma]] *)
  [@@deriving sexp, equal, compare, hash]

  val var : Var.t -> t
  val ( @-> ) : t -> t -> t
  val constr : t list -> Ident.t -> t
  val tuple : t list -> t
  val shape : t list -> Principal_shape.t -> t
  val poly : Type_scheme.t -> t

  module Matchee : sig
    (** [t] is a matchee, a principal shape of the type being matched. 
        The shape quantifiers are implicitly bound. *)
    type t =
      | Arrow of Var.t * Var.t
      | Tuple of Var.t list
      | Constr of Var.t list * Ident.t
      | Poly of Type_scheme.t
    [@@deriving sexp]
  end
end = struct
  (* TODO():

     This isn't a perfect fit since we can create types with nonsense names
     But the code re-use is nice :) *)
  module Ident = Var.Make (struct
      let module_name = "Type.Ident"
    end)

  module Var = Var.Make (struct
      let module_name = "Type.Var"
    end)

  type t =
    | Var of Var.t
    | Arrow of t * t
    | Tuple of t list
    | Constr of t list * Ident.t
    | Shape of t list * Principal_shape.t
    | Poly of Type_scheme.t
  [@@deriving sexp, equal, compare, hash]

  let var v = Var v
  let ( @-> ) t1 t2 = Arrow (t1, t2)
  let constr ts constr = Constr (ts, constr)
  let tuple ts = Tuple ts
  let shape ts sh = Shape (ts, sh)
  let poly scm = Poly scm

  module Matchee = struct
    type t =
      | Arrow of Var.t * Var.t
      | Tuple of Var.t list
      | Constr of Var.t list * Ident.t
      | Poly of Type_scheme.t
    [@@deriving sexp]
  end
end

and Type_scheme : sig
  (** [t] represents a polymorphic type [forall 'a1, ..., 'an. tau] *)
  type t =
    { quantifiers : Type.Var.t list
    ; body : Type.t
    }
  [@@deriving sexp, equal, compare, hash]

  val create : ?quantifiers:Type.Var.t list -> Type.t -> t
end = struct
  type t =
    { quantifiers : Type.Var.t list
    ; body : Type.t
    }
  [@@deriving sexp, equal, compare, hash]

  let create ?(quantifiers = []) body = { quantifiers; body }
end

and Principal_shape : sig
  module Poly : sig
    type t =
      { quantifiers : Type.Var.t list
      ; scheme : Type_scheme.t
      }
    [@@deriving sexp, equal, compare, hash]

    include Invariant.S with type t := t

    val create : ?quantifiers:Type.Var.t list -> Type_scheme.t -> t

    val create_unchecked : ?quantifiers:Type.Var.t list -> Type_scheme.t -> t
    [@@alert
      unsafe "Safety: this function does not guarantee that the poly shape is principal"]
  end

  type t =
    | Sh_arrow (** Arrow shape ['c1 'c2. 'c1 -> 'c2] *)
    | Sh_tuple of int (** Tuple shape ['c1, ..., 'cn. 'c1 * ... * 'cn] *)
    | Sh_constr of int * Type.Ident.t
    (** Nominal type shape ['c1, ..., 'cn. ('c1, ..., 'cn) T] *)
    | Sh_poly of Poly.t (** Polytype shape ['c1, ..., 'cn. [sigma]] *)
  [@@deriving sexp, equal, compare, hash]
end = struct
  module Poly = struct
    type t =
      { quantifiers : Type.Var.t list
      ; scheme : Type_scheme.t
      }
    [@@deriving sexp, equal, compare, hash]

    let create_unchecked ?(quantifiers = []) scheme = { quantifiers; scheme }

    let invariant t =
      Invariant.invariant [%here] t [%sexp_of: t] (fun () ->
        let shape_quantifiers = Type.Var.Hash_set.of_list t.quantifiers in
        let scheme_quantifiers = Type.Var.Hash_set.of_list t.scheme.quantifiers in
        let num_quantifiers =
          Hash_set.length shape_quantifiers + Hash_set.length scheme_quantifiers
        in
        (* Invariant: all quantifiers are canonical. They are named using [0, num_quantifiers).  *)
        let check_canonical_names () =
          let marks = Array.create ~len:num_quantifiers false in
          let check_canonical_name (var : Type.Var.t) =
            assert (String.(var.name = "Principal_shape.Var"));
            let idx = (var.id :> int) in
            assert (not marks.(idx));
            marks.(idx) <- true
          in
          List.iter t.quantifiers ~f:check_canonical_name;
          List.iter t.scheme.quantifiers ~f:check_canonical_name;
          (* All variables are within [0, num_quantifiers). No duplicates *)
          assert (Array.for_all marks ~f:Fun.id)
        in
        let check_scheme_body () =
          let uses = Array.create ~len:num_quantifiers 0 in
          let[@inline] mark_use (var : Type.Var.t) =
            let idx = (var.id :> int) in
            uses.(idx) <- uses.(idx) + 1
          in
          let[@inline] num_uses (var : Type.Var.t) = uses.((var.id :> int)) in
          let[@inline] is_polyshape (shape : Principal_shape.t) =
            match shape with
            | Sh_arrow | Sh_tuple _ | Sh_constr _ -> false
            | Sh_poly _ -> true
          in
          (* We rely on non-short-circuting operators (since marking uses is effectful) *)
          let ( ||| ) a b = a || b in
          let non_short_circuiting_exists xs ~f =
            List.fold xs ~init:false ~f:(fun acc x -> acc ||| f x)
          in
          (* Traverses the type checking invariants. Returns [true] if it contains a polymorphic part. *)
          let rec loop (type_ : Type.t) : bool =
            match type_ with
            | Var var ->
              mark_use var;
              Hash_set.mem scheme_quantifiers var
            | Arrow (type1, type2) ->
              (* Invariant: all constructors must contain a polymorphic subterm. *)
              assert (loop type1 ||| loop type2);
              true
            | Tuple types | Constr (types, _) ->
              (* Invariant: ditto. *)
              assert (non_short_circuiting_exists types ~f:loop);
              true
            | Poly _ ->
              (* Invariant: no occurrences of [Poly]. *)
              assert false
            | Shape (types, shape) ->
              (* Invariant: all shapes applications must contain a polymorphic subterm. *)
              assert (non_short_circuiting_exists types ~f:loop);
              (* Invariant: all shapes must be polyshapes. *)
              assert (is_polyshape shape);
              true
          in
          (* Invariant: body is skeletal *)
          ignore (loop t.scheme.body : bool);
          (* Invariant: shape quantifiers are linear (i.e. used exactly once). *)
          Hash_set.iter shape_quantifiers ~f:(fun var -> assert (num_uses var = 1));
          (* Invariant: all scheme quantifiers are used at least once. *)
          Hash_set.iter scheme_quantifiers ~f:(fun var -> assert (num_uses var >= 1))
        in
        check_canonical_names ();
        check_scheme_body ())
    ;;

    let create ?quantifiers scheme =
      let t = create_unchecked ?quantifiers scheme in
      invariant t;
      t
    ;;
  end

  type t =
    | Sh_arrow
    | Sh_tuple of int
    | Sh_constr of int * Type.Ident.t
    | Sh_poly of Poly.t
  [@@deriving sexp, equal, compare, hash]
end

module Var = Var.Make (struct
    let module_name = "Constraint.Var"
  end)

module Closure = struct
  type t =
    { type_vars : Type.Var.t list
    ; vars : Var.t list
    }
  [@@deriving sexp]

  let of_list type_or_schemes =
    let type_vars, vars =
      List.partition_map type_or_schemes ~f:(function
        | `Type type_var -> First type_var
        | `Scheme var -> Second var)
    in
    { type_vars; vars }
  ;;
end

type t =
  | True
  | False of Mlsus_error.t
  | Conj of t * t
  | Eq of Type.t * Type.t
  | Exists of Type.Var.t * t
  | Let of Var.t * scheme * t
  | Instance of Var.t * Type.t
  | Match of
      { matchee : Type.Var.t
      ; closure : Closure.t
      ; case : Type.Matchee.t -> t
      ; else_ : unit -> t
      }
  | With_range of t * Range.t

and scheme =
  { type_vars : (flexibility * Type.Var.t) list
  ; in_ : t
  ; type_ : Type.t
  }

and flexibility =
  | Flexible
  | Rigid
[@@deriving sexp]

let tt = True
let ff err = False err
let ( &~ ) t1 t2 = Conj (t1, t2)

let all ts =
  match ts with
  | [] -> tt
  | [ t ] -> t
  | ts -> List.fold ts ~init:tt ~f:( &~ )
;;

let ( =~ ) type1 type2 = Eq (type1, type2)
let exists type_var t = Exists (type_var, t)
let exists_many vars in_ = List.fold_right vars ~init:in_ ~f:exists
let ( #= ) x scheme = x, scheme
let mono_scheme type_ = { type_vars = []; in_ = tt; type_ }
let ( @=> ) t1 t2 = t1, t2
let ( @. ) t1 t2 = t1, t2
let poly_scheme (type_vars, (in_, type_)) = { type_vars; in_; type_ }
let let_ (x, scheme) ~in_ = Let (x, scheme, in_)
let inst x type_ = Instance (x, type_)

let match_ matchee ~closure ~with_ ~else_ =
  Match { matchee; closure = Closure.of_list closure; case = with_; else_ }
;;

let with_range t ~range = With_range (t, range)

module Quickcheckable = struct
  [@@@warning "-30"]

  type type_ = Type.t =
    | Var of Type.Var.t
    | Arrow of type_ * type_
    | Tuple of type_ list
    | Constr of type_ list * Type.Ident.t
    | Shape of type_ list * principal_shape
    | Poly of type_scheme
  [@@deriving quickcheck]

  and poly_principal_shape = Principal_shape.Poly.t =
    { quantifiers : Type.Var.t list
    ; scheme : type_scheme
    }
  [@@deriving quickcheck]

  and type_scheme = Type_scheme.t =
    { quantifiers : Type.Var.t list
    ; body : type_
    }
  [@@deriving quickcheck]

  and principal_shape = Principal_shape.t =
    | Sh_arrow [@quickcheck.do_not_generate]
    | Sh_tuple of int
    | Sh_constr of int * Type.Ident.t
    | Sh_poly of poly_principal_shape [@quickcheck.do_not_generate]
  [@@deriving quickcheck]

  module Type = struct
    let quickcheck_generator = quickcheck_generator_type_
    let quickcheck_shrinker = quickcheck_shrinker_type_
    let quickcheck_observer = quickcheck_observer_type_
  end

  module Type_scheme = struct
    let quickcheck_generator = quickcheck_generator_type_scheme
    let quickcheck_shrinker = quickcheck_shrinker_type_scheme
    let quickcheck_observer = quickcheck_observer_type_scheme
  end

  module Principal_shape = struct
    (* We don't generate poly or arrow shapes due to the invariants that come with them. *)
    let quickcheck_generator = quickcheck_generator_principal_shape
    let quickcheck_shrinker = quickcheck_shrinker_principal_shape
    let quickcheck_observer = quickcheck_observer_principal_shape
  end
end
