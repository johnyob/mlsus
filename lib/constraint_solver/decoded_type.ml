open! Import
module Type = Generalization.Type

module Var = Var.Make (struct
    let module_name = "Decoded_type.Var"
  end)

module Ident = Constraint.Type.Ident

type t =
  | Var of Var.t
  | Arrow of t * t
  | Tuple of t list
  | Constr of t list * Ident.t
  | Mu of Var.t * t
[@@deriving sexp]

let pp ppf t =
  let var_to_name (var : Var.t) =
    let id = (var.id :> int) in
    let char = String.make 1 (Char.of_int_exn (Char.to_int 'a' + (id mod 26))) in
    let suffix = id / 26 in
    if suffix = 0 then char else char ^ Int.to_string suffix
  in
  let ident_to_name (ident : Ident.t) =
    String.split_on_chars ~on:[ '.' ] ident.name |> List.last_exn
  in
  let rec pp_mu ppf t =
    match t with
    | Mu (var, t) -> Fmt.pf ppf "@[%a@ as %a@]" pp_mu t pp_var var
    | t -> pp_arrow ppf t
  and pp_arrow ppf t =
    match t with
    | Arrow (t1, t2) -> Fmt.pf ppf "@[%a ->@ %a@]" pp_tuple t1 pp_arrow t2
    | t -> pp_tuple ppf t
  and pp_tuple ppf t =
    match t with
    | Tuple ts -> Fmt.(pf ppf "@[<0>%a@]" (list ~sep:(any " *@ ") pp_atom) ts)
    | t -> pp_atom ppf t
  and pp_atom ppf t =
    match t with
    | Var var -> pp_var ppf var
    | Constr (ts, constr) ->
      let pp_args ppf ts =
        match ts with
        | [] -> ()
        | [ t ] -> Fmt.pf ppf "%a@ " pp_atom t
        | ts -> Fmt.(pf ppf "@[(%a)@ @]" (list ~sep:comma pp_mu) ts)
      in
      Fmt.(pf ppf "@[%a%s@]" pp_args ts (ident_to_name constr))
    | Arrow _ | Mu _ | Tuple _ -> Fmt.(parens pp_mu ppf t)
  and pp_var ppf (var : Var.t) = Fmt.pf ppf "'%s" (var_to_name var) in
  pp_mu ppf t
;;

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

  type nonrec t = Type.t -> t

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
        let structure = Type.structure type_ in
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
        | Arrow (gtype1, gtype2) ->
          (* The let bindings here are to ensure evaluation order, 
             which corresponds to allocating fresh variables from left to right *)
          let dtype1 = decode gtype1 in
          let dtype2 = decode gtype2 in
          Arrow (dtype1, dtype2)
        | Tuple gtypes -> Tuple (List.map gtypes ~f:decode)
        | Constr (gtypes, constr_ident) -> Constr (List.map gtypes ~f:decode, constr_ident)
      in
      decode gtype
  ;;
end
