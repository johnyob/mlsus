open! Import
module C = Constraint

(* TODO: Have optimized type for solver which includes a hash for poly_shapes. 
         This will provide a cheap equality function for unification. *)

include C.Principal_shape

let create_var ~id_source () = C.Type.Var.create ~id_source ~name:"Principal_shape.Var" ()

let quantifiers t =
  match t with
  | Sh_arrow ->
    (* Invariant: All quantifiers are locally named from 0 to n *)
    let id_source = Identifier.create_source () in
    (* [let]s are used to force the correct ordering *)
    let var1 = create_var ~id_source () in
    let var2 = create_var ~id_source () in
    [ var1; var2 ]
  | Sh_tuple n | Sh_constr (n, _) ->
    (* Invariant: All quantifiers are locally named from 0 to n *)
    let id_source = Identifier.create_source () in
    List.init n ~f:(fun _ -> create_var ~id_source ())
  | Sh_poly poly_shape -> poly_shape.quantifiers
;;

module Poly_shape_decomposition = struct
  open C

  module State = struct
    type t =
      { id_source : (Identifier.source[@sexp.opaque])
      ; shape_decomposition : Type.t Type.Var.Table.t
      ; scheme_variable_renaming : Type.Var.t Type.Var.Table.t
      ; scheme_quantifiers : Type.Var.Set.t
      }
    [@@deriving sexp]

    let create scheme_quantifiers =
      { shape_decomposition = Type.Var.Table.create ()
      ; scheme_variable_renaming = Type.Var.Table.create ()
      ; id_source = Identifier.create_source ()
      ; scheme_quantifiers
      }
    ;;

    let alloc_var t = create_var ~id_source:t.id_source ()

    let rename_scheme_var t var =
      Hashtbl.find_or_add t.scheme_variable_renaming var ~default:(fun () -> alloc_var t)
    ;;

    let alloc_shape_decomposition t type_ =
      let var = alloc_var t in
      Hashtbl.set t.shape_decomposition ~key:var ~data:type_;
      var
    ;;
  end

  module Polymorphic_or_monomorphic_part = struct
    type t =
      | Polymorphic of { principal_part : Type.t }
      (** [Polymorphic { principal_part }] indicates that original type is a polymorphic body part. 
          [principal_part] is the transformed part.  *)
      | Monomorphic
      (** [Monomorphic] indicates that the original type is a monomorphic body part. *)
    [@@deriving sexp]

    let is_monomorphic t =
      match t with
      | Polymorphic _ -> false
      | Monomorphic -> true
    ;;

    module With_original = struct
      type nonrec t =
        { result : t
        ; original : Type.t
        }
      [@@deriving sexp]

      let principal_part t ~state =
        match t.result with
        | Polymorphic { principal_part } -> principal_part
        | Monomorphic -> Var (State.alloc_shape_decomposition state t.original)
      ;;

      let[@inline] is_monomorphic t = is_monomorphic t.result
    end

    let map_principal_part2 (t1 : With_original.t) (t2 : With_original.t) ~f ~state =
      match t1.result, t2.result with
      | Monomorphic, Monomorphic -> Monomorphic
      | _, _ ->
        let type1 = With_original.principal_part t1 ~state in
        let type2 = With_original.principal_part t2 ~state in
        Polymorphic { principal_part = f type1 type2 }
    ;;

    let map_principal_parts (ts : With_original.t list) ~f ~state =
      if List.for_all ts ~f:With_original.is_monomorphic
      then Monomorphic
      else (
        let types = List.map ts ~f:(With_original.principal_part ~state) in
        Polymorphic { principal_part = f types })
    ;;
  end

  let of_applied_shape (shape : Principal_shape.t) types : Type.t =
    (* All applied shapes are normalized (aside from polytypes) *)
    match shape with
    | Sh_tuple _ -> Tuple types
    | Sh_constr (_, constr) -> Constr (types, constr)
    | Sh_arrow ->
      (match types with
       | [ type1; type2 ] -> Arrow (type1, type2)
       | _ -> assert false)
    | Sh_poly _ -> Shape (types, shape)
  ;;

  let rec of_scheme_body ~(state : State.t) (type_ : Type.t)
    : Polymorphic_or_monomorphic_part.t
    =
    let module Part = Polymorphic_or_monomorphic_part in
    let self = of_scheme_body ~state in
    let self_with_original type_ : Part.With_original.t =
      { result = self type_; original = type_ }
    in
    match type_ with
    | Var v ->
      if Set.mem state.scheme_quantifiers v
      then Polymorphic { principal_part = Var (State.rename_scheme_var state v) }
      else Monomorphic
    | Arrow (t1, t2) ->
      Part.map_principal_part2
        (self_with_original t1)
        (self_with_original t2)
        ~state
        ~f:(fun t1 t2 -> Arrow (t1, t2))
    | Tuple ts ->
      Part.map_principal_parts (List.map ts ~f:self_with_original) ~state ~f:(fun ts ->
        Tuple ts)
    | Constr (ts, constr) ->
      Part.map_principal_parts (List.map ts ~f:self_with_original) ~state ~f:(fun ts ->
        Constr (ts, constr))
    | Shape (ts, shape) ->
      Part.map_principal_parts (List.map ts ~f:self_with_original) ~state ~f:(fun ts ->
        of_applied_shape shape ts)
    | Poly scm ->
      let ts, poly_shape = of_scheme scm in
      Part.map_principal_parts (List.map ts ~f:self_with_original) ~state ~f:(fun ts ->
        Shape (ts, Sh_poly poly_shape))

  and of_scheme ({ quantifiers; body } : Type_scheme.t) : Type.t list * Poly.t =
    let state = State.create (Type.Var.Set.of_list quantifiers) in
    let scheme_body =
      let result = of_scheme_body ~state body in
      Polymorphic_or_monomorphic_part.With_original.principal_part
        { result; original = body }
        ~state
    in
    let shape_quantifiers, types =
      Hashtbl.to_alist state.shape_decomposition
      |> List.sort ~compare:(Comparable.lift Type.Var.compare ~f:fst)
      |> List.unzip
    in
    let scheme_quantifiers =
      Hashtbl.data state.scheme_variable_renaming |> List.sort ~compare:Type.Var.compare
    in
    ( types
    , (* Safety should be guaranteed by construction *)
      (Poly.create_unchecked
         ~quantifiers:shape_quantifiers
         (Type_scheme.create ~quantifiers:scheme_quantifiers scheme_body)
       [@alert "-unsafe"]) )
  ;;
end

let poly_shape_decomposition_of_scheme = Poly_shape_decomposition.of_scheme

include Comparable.Make (Constraint.Principal_shape)
