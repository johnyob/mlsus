open! Import
module Scheme_skeleton_ident = Constraint.Type.Scheme_skeleton_ident

type t =
  { closure : Constraint.Type.Var.t list
  ; skeleton : Scheme_skeleton_ident.t
  }
[@@deriving sexp]

module Canonicalized_type = struct
  module Var = struct
    type t =
      { kind : kind
      ; id : Identifier.t
      }
    [@@deriving equal, compare, sexp, hash]

    and kind =
      | Polymorphic
      | Monomorphic
    [@@deriving equal, compare, sexp, hash]
  end

  type t =
    | Var of Var.t
    | App of t * t
    | Spine of t list
    | Head of Constraint.Type.Head.t
  [@@deriving equal, compare, sexp, hash]
end

module State = struct
  type t = { skeleton_tbl : (Canonicalized_type.t, Scheme_skeleton_ident.t) Hashtbl.t }
  [@@unboxed] [@@deriving sexp_of]

  let create () = { skeleton_tbl = Hashtbl.create (module Canonicalized_type) }

  let find_or_add_skeleton t canonicalized_body ~closure ~scheme ~alloc_skeleton =
    Hashtbl.find_or_add t.skeleton_tbl canonicalized_body ~default:(fun () ->
      alloc_skeleton ~closure ~scheme)
  ;;
end

module Of_constraint_scheme = struct
  module C = Constraint

  module Local_state = struct
    type t =
      { variable_renaming : Identifier.t C.Type.Var.Table.t
      ; id_source : (Identifier.source[@sexp.opaque])
      ; quantifiers : C.Type.Var.Set.t
      }
    [@@deriving sexp]

    let create ?(quantifiers = C.Type.Var.Set.empty) () =
      { variable_renaming = C.Type.Var.Table.create ()
      ; id_source = Identifier.create_source ()
      ; quantifiers
      }
    ;;

    let rename_var t var =
      let id =
        Hashtbl.find_or_add t.variable_renaming var ~default:(fun () ->
          Identifier.create t.id_source)
      in
      let kind =
        if Set.mem t.quantifiers var
        then Canonicalized_type.Var.Polymorphic
        else Monomorphic
      in
      Canonicalized_type.Var.{ kind; id }
    ;;

    let closure t =
      Hashtbl.keys t.variable_renaming
      |> List.filter ~f:(fun var -> not (Set.mem t.quantifiers var))
    ;;
  end

  let rec canonicalize_type
            ~(state : State.t)
            ~alloc_skeleton
            ~(lstate : Local_state.t)
            (type_ : C.Type.t)
    : Canonicalized_type.t
    =
    let self = canonicalize_type ~state ~alloc_skeleton ~lstate in
    let rename_var var = Canonicalized_type.Var (Local_state.rename_var lstate var) in
    match type_ with
    | Var var -> rename_var var
    | App (type1, type2) -> App (self type1, self type2)
    | Head hd -> Head hd
    | Spine types -> Spine (List.map types ~f:self)
    | Defunctionalized_scheme scm ->
      let { closure; skeleton } = defunctionalize_scheme ~state ~alloc_skeleton scm in
      App (Spine (List.map closure ~f:rename_var), Head (Scheme skeleton))

  and defunctionalize_scheme ~state ~alloc_skeleton (scm : C.Type.scheme) : t =
    let quantifiers = C.Type.Var.Set.of_list scm.scheme_quantifiers in
    let lstate = Local_state.create ~quantifiers () in
    let canonicalized_body =
      canonicalize_type ~state ~alloc_skeleton ~lstate scm.scheme_body
    in
    let closure = Local_state.closure lstate in
    let skeleton =
      State.find_or_add_skeleton
        state
        canonicalized_body
        ~closure
        ~scheme:scm
        ~alloc_skeleton
    in
    { skeleton; closure }
  ;;
end

let of_constraint_scheme = Of_constraint_scheme.defunctionalize_scheme
