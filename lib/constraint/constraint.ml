open Core
open Mlsus_std
open Grace

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

  module Head = struct
    module T = struct
      type t =
        | Arrow
        | Tuple of int
        | Constr of Ident.t
      [@@deriving equal, compare, hash, sexp]
    end

    include T
    include Comparable.Make (T)
  end

  module Matchee = struct
    type t =
      | App of Var.t * Var.t
      | Head of Head.t
      | Spine of Var.t list
      | Rigid_var
    [@@deriving sexp]
  end

  type t =
    | Head of Head.t
    | App of t * t
    | Spine of t list
    | Var of Var.t
  [@@deriving sexp]

  let var v = Var v
  let ( @-> ) t1 t2 = App (Spine [ t1; t2 ], Head Arrow)
  let constr ts constr = App (Spine ts, Head (Constr constr))
  let tuple ts = App (Spine ts, Head (Tuple (List.length ts)))
  let spine ts = Spine ts
  let ( @% ) t1 t2 = App (t1, t2)
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
