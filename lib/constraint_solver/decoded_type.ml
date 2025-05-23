open! Import
module C = Constraint
module G = Generalization

module Var = Var.Make (struct
    let module_name = "Decoded_type.Var"
  end)

type t =
  | Var of Var.t
  | Shape of Principal_shape.t
  | Spine of t list
  | App of t * t
  | Mu of Var.t * t
[@@deriving sexp]

module Pretter_printer = struct
  let id_to_var_name (id : Identifier.t) =
    let id = (id :> int) in
    let char = String.make 1 (Char.of_int_exn (Char.to_int 'a' + (id mod 26))) in
    let suffix = id / 26 in
    if suffix = 0 then char else char ^ Int.to_string suffix
  ;;

  let[@inline] pp_ident ppf (ident : C.Type.Ident.t) =
    Fmt.string ppf (String.split_on_chars ~on:[ '.' ] ident.name |> List.last_exn)
  ;;

  let[@inline] pp_arrow pp_lhs pp_rhs ppf (lhs, rhs) =
    Fmt.pf ppf "@[%a ->@ %a@]" pp_lhs lhs pp_rhs rhs
  ;;

  let[@inline] pp_tuple pp_type ppf types =
    Fmt.(pf ppf "@[<0>%a@]" (list ~sep:(any " *@ ") pp_type) types)
  ;;

  let[@inline] pp_constr pp_args ppf (types, ident) =
    Fmt.(pf ppf "@[%a%a@]") pp_args types pp_ident ident
  ;;

  let[@inline] pp_applied_shape pp_args pp_shape ppf (types, shape) =
    Fmt.(pf ppf "@[%a%a@]") pp_args types pp_shape shape
  ;;

  let pp_args ~in_app ~pp_atom ~pp ppf ts =
    if in_app
    then (
      match ts with
      | [] -> ()
      | [ t ] -> Fmt.pf ppf "%a@ " pp_atom t
      | ts -> Fmt.(pf ppf "@[(%a)@ @]" (list ~sep:comma pp) ts))
    else Fmt.(pf ppf "@[(%a)@]" (list ~sep:comma pp) ts)
  ;;

  module Constraint_type = struct
    let[@inline] pp_var ppf (var : C.Type.Var.t) =
      let name = id_to_var_name var.id in
      Fmt.pf ppf "'%s" name
    ;;

    let rec pp ppf (t : C.Type.t) =
      let rec pp_lvl_arrow ppf (t : C.Type.t) =
        match t with
        | Arrow (t1, t2) | Shape ([ t1; t2 ], Sh_arrow) ->
          pp_arrow pp_lvl_tuple pp_lvl_arrow ppf (t1, t2)
        | t -> pp_lvl_tuple ppf t
      and pp_lvl_tuple ppf (t : C.Type.t) =
        match t with
        | Tuple ts | Shape (ts, Sh_tuple _) -> pp_tuple pp_lvl_app ppf ts
        | t -> pp_lvl_app ppf t
      and pp_lvl_app ppf (t : C.Type.t) =
        match t with
        | Constr (ts, constr) | Shape (ts, Sh_constr (_, constr)) ->
          pp_constr pp_lvl_args ppf (ts, constr)
        | Shape (ts, shape) -> pp_applied_shape pp_lvl_args pp_shape ppf (ts, shape)
        | t -> pp_lvl_atom ppf t
      and pp_lvl_args ppf ts =
        pp_args ~in_app:true ~pp_atom:pp_lvl_atom ~pp:pp_lvl_arrow ppf ts
      and pp_lvl_atom ppf t =
        match t with
        | Var var -> pp_var ppf var
        | Poly scheme -> Fmt.pf ppf "@[[%a]@]" pp_scheme scheme
        | t -> Fmt.parens pp_lvl_arrow ppf t
      in
      pp_lvl_arrow ppf t

    and pp_shape ppf (shape : Principal_shape.t) =
      match shape with
      | Sh_arrow -> Fmt.string ppf "(->)"
      | Sh_tuple n -> Fmt.pf ppf "Pi^%d" n
      | Sh_constr (n, constr) -> Fmt.pf ppf "%a(%d)" pp_ident constr n
      | Sh_poly { quantifiers; scheme } ->
        Fmt.pf
          ppf
          "@[(@[<hov 2>ν%a.@ %a@])@]"
          Fmt.(list ~sep:comma pp_var)
          quantifiers
          pp_scheme
          scheme

    and pp_scheme ppf scheme =
      let { C.Type_scheme.quantifiers; body } = scheme in
      Fmt.pf ppf "@[<hov 2>%a.@ %a@]" Fmt.(list ~sep:comma pp_var) quantifiers pp body
    ;;
  end

  module Decoded_type = struct
    let[@inline] pp_var ppf (var : Var.t) =
      let name = id_to_var_name var.id in
      Fmt.pf ppf "'%s" name
    ;;

    let pp ppf t =
      let rec pp_lvl_mu ppf t =
        match t with
        | Mu (var, t) -> Fmt.pf ppf "@[%a@ as %a@]" pp_lvl_mu t pp_var var
        | t -> pp_lvl_arrow ppf t
      and pp_lvl_arrow ppf t =
        match t with
        | App (Spine [ t1; t2 ], Shape Sh_arrow) ->
          pp_arrow pp_lvl_tuple pp_lvl_arrow ppf (t1, t2)
        | t -> pp_lvl_tuple ppf t
      and pp_lvl_tuple ppf t =
        match t with
        | App (Spine ts, Shape (Sh_tuple _)) -> pp_tuple pp_lvl_app ppf ts
        | t -> pp_lvl_app ppf t
      and pp_lvl_app ppf t =
        match t with
        | App (_, Shape (Sh_tuple _ | Sh_arrow)) -> Fmt.(parens pp_lvl_arrow ppf t)
        | App (t, Shape (Sh_constr (_, constr))) ->
          pp_constr (pp_lvl_spine ~in_app:true) ppf (t, constr)
        | App (t1, t2) ->
          pp_applied_shape (pp_lvl_spine ~in_app:true) pp_lvl_atom ppf (t1, t2)
        | t -> pp_lvl_spine ~in_app:false ppf t
      and pp_lvl_spine ~in_app ppf t =
        match t with
        | Spine ts -> pp_args ~in_app ~pp_atom:pp_lvl_atom ~pp:pp_lvl_mu ppf ts
        | t -> pp_lvl_atom ppf t
      and pp_lvl_atom ppf t =
        match t with
        | Var var -> pp_var ppf var
        | Shape sh -> Constraint_type.pp_shape ppf sh
        | App _ | Mu _ | Spine _ -> Fmt.(parens pp_lvl_mu ppf t)
      in
      pp_lvl_mu ppf t
    ;;
  end
end

let pp = Pretter_printer.Decoded_type.pp

module Decoder = struct
  module State = struct
    type t =
      { id_source : Identifier.source
        (** An identifier source used to allocate variables *)
      ; variable_renaming : (Identifier.t, Var.t) Hashtbl.t
        (** A mapping from variable structure identifiers to allocated variables *)
      }

    let create () =
      { id_source = Identifier.create_source ()
      ; variable_renaming = Hashtbl.create (module Identifier)
      }
    ;;

    let alloc_var t = Var.create ~id_source:t.id_source ()

    let rename_var t id =
      Hashtbl.find_or_add t.variable_renaming id ~default:(fun () -> alloc_var t)
    ;;
  end

  type nonrec t = G.Type.t -> t

  type status =
    | Active (** A node is actively being visited. *)
    | Cyclical of Var.t
    (** A cyclical node with an allocated variable (for a mu-binder). *)
  [@@deriving sexp_of]

  let create () : t =
    let state = State.create () in
    fun gtype ->
      let visited_table = Hashtbl.create (module Identifier) in
      (* Recursive loop that traverses the graphical type *)
      let rec decode type_ =
        let structure = G.Type.structure type_ in
        let id = structure.id in
        match Hashtbl.find visited_table id with
        | Some (Cyclical var) ->
          (* Node is cyclic, use allocated variable *)
          Var var
        | Some Active ->
          let var = State.alloc_var state in
          (* Mark the node as being cyclic.
             Allocate a variable to represent cyclic positions *)
          Hashtbl.set visited_table ~key:id ~data:(Cyclical var);
          Var var
        | None ->
          (* Mark the node as being visited *)
          Hashtbl.set visited_table ~key:id ~data:Active;
          (* Visit children *)
          let result = decode_first_order_structure ~id structure.inner in
          (* Safety: Cannot through an exception since the visited table
             must have an entry for this node. *)
          let status = Hashtbl.find_exn visited_table id in
          Hashtbl.remove visited_table id;
          (match status with
           | Cyclical var -> Mu (var, result)
           | Active -> result)
      and decode_first_order_structure ~id structure =
        match structure with
        | Var _ -> Var (State.rename_var state id)
        | Structure s -> decode_rigid_structure ~id s
      and decode_rigid_structure ~id structure =
        match structure with
        | Rigid_var -> Var (State.rename_var state id)
        | Structure former -> decode_former former
      and decode_former former =
        match former with
        | App (gtype1, gtype2) ->
          (* The let bindings here are to ensure evaluation order,
             which corresponds to allocating fresh variables from left to right *)
          let dtype1 = decode gtype1 in
          let dtype2 = decode gtype2 in
          App (dtype1, dtype2)
        | Spine gtypes -> Spine (List.map gtypes ~f:decode)
        | Shape sh -> Shape sh
      in
      decode gtype
  ;;
end
