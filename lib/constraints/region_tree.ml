open! Import
include Region_tree_intf

module Make (R : T1_with_sexp_of) = struct
  type 'a node =
    { id : Identifier.t
    ; parent : 'a node option
    ; level : Level.t
    ; region : 'a R.t
    }
  [@@deriving sexp_of]

  and 'a t = T of 'a node [@@unboxed] [@@deriving sexp_of]

  let root (T root) = root

  let create ~id_source ~region =
    T { id = Identifier.create id_source; parent = None; level = Level.zero; region }
  ;;

  let create_node ~id_source ~parent ~region =
    let level = Level.enter parent.level in
    { id = Identifier.create id_source; parent = Some parent; level; region }
  ;;

  let rec nearest_common_ancestor t1 t2 =
    if Identifier.(t1.id = t2.id)
    then t1
    else if Level.(t1.level < t2.level)
    then nearest_common_ancestor t1 (Option.value_exn ~here:[%here] t2.parent)
    else if Level.(t1.level > t2.level)
    then nearest_common_ancestor (Option.value_exn ~here:[%here] t1.parent) t2
    else (
      assert (Level.(t1.level = t2.level && t1.level > zero));
      nearest_common_ancestor
        (Option.value_exn ~here:[%here] t1.parent)
        (Option.value_exn ~here:[%here] t2.parent))
  ;;

  let unsafe_max_by_level ts =
    match ts with
    | [] -> assert false
    | t :: ts ->
      List.fold ts ~init:t ~f:(fun t1 t2 ->
        if Level.(t1.level < t2.level) then t2 else t1)
  ;;

  module Path = struct
    type 'a t =
      { dst : 'a node
      ; compare_node_by_level : 'a node -> 'a node -> int
      ; mem : 'a node -> bool
      }
    [@@deriving sexp_of]

    let of_node dst =
      let node_by_level = Hashtbl.create (module Level) in
      let rec populate_levels node =
        Hashtbl.set node_by_level ~key:node.level ~data:node;
        match node.parent with
        | None -> ()
        | Some parent_node -> populate_levels parent_node
      in
      populate_levels dst;
      let mem node =
        match Hashtbl.find_exn node_by_level node.level with
        | exception Not_found_s _ -> false
        | node' -> Identifier.(node.id = node'.id)
      in
      let compare_node_by_level n1 n2 =
        assert (mem n1 && mem n2);
        Level.compare n1.level n2.level
      in
      { dst; mem; compare_node_by_level }
    ;;

    let compare_node_by_level t n1 n2 = t.compare_node_by_level n1 n2 [@@inline]
    let mem t n = t.mem n [@@inline]
    let dst t = t.dst [@@inline]
  end
end
