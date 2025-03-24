open Core
open Mlsus_std

module Type = struct
  (* TODO():

     This isn't a perfect fit since we can create types with nonsense names
     But the code re-use is nice :) *)
  module Ident = Var.Make (struct
      let module_name = "Type.Ident"
    end)

  module Var = Var.Make (struct
      let module_name = "Type.Var"
    end)

  module Matchee = struct
    (** [t] is a matchee, a partial (shallow) type that is matched on. *)
    type t =
      | Arrow of Var.t * Var.t
      | Tuple of Var.t list
      | Constr of Var.t list * Ident.t
    [@@deriving sexp]
  end

  type t =
    | Arrow of t * t
    | Tuple of t list
    | Constr of t list * Ident.t
    | Var of Var.t
  [@@deriving sexp]

  let var v = Var v
  let ( @-> ) t1 t2 = Arrow (t1, t2)
  let constr ts constr = Constr (ts, constr)
  let tuple ts = Tuple ts
end

module Var = Var.Make (struct
    let module_name = "Constraint.Var"
  end)

module Closure = struct
  type t = { type_vars : Type.Var.Set.t } [@@unboxed] [@@deriving sexp]

  let of_list type_vars = { type_vars = Type.Var.Set.of_list type_vars }
end

type t =
  | True
  | False of Mlsus_error.t
  | Conj of t * t
  | Eq of Type.t * Type.t
  | Exists of Type.Var.t * t
  | Let of Var.t * scheme * t
  | Instance of Var.t * Type.t
  | Match of Type.Var.t * Closure.t * (Type.Matchee.t -> t)

and scheme =
  { type_vars : Type.Var.t list
  ; in_ : t
  ; type_ : Type.t
  }
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
let match_ a ~closure ~with_ = Match (a, Closure.of_list closure, with_)
