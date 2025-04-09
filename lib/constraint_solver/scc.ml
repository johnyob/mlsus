open! Import

module Make (G : sig
    type t

    module Node : sig
      type t [@@deriving sexp_of, compare, hash]
    end

    val iter_nodes : t -> f:(Node.t -> unit) -> unit
    val iter_succ : t -> Node.t -> f:(Node.t -> unit) -> unit
  end) =
struct
  open G

  type data =
    { idx : int
      (** Each [node] is associated with an index. The indexes represent the 
          order in which nodes were discovered. *)
    ; mutable low_idx : int
      (** Each [node] stores the lowest index associated to a node within 
          [node]'s SCC. *)
    ; mutable stacked : bool (** [stacked] is [true] if the node is in the SCC stack. *)
    ; mutable scc_id : int (** Each [node] is eventually associated with an SCC. *)
    ; mutable contains_outside_edge : bool
    }
  [@@deriving sexp_of]

  type state =
    { mutable sccs : Node.t list list
    ; table : (Node.t, data) Hashtbl.t
    ; mutable leaf_sccs : Node.t list list
    }
  [@@deriving sexp_of]

  (* A leaf SCC is defined as an SCC in which for all nodes [n] in the SCC, 
     there doesn't exist an [(n, m)] where [m] is in a different SCC. In the guard graph, 
     this means the SCC is dependent on any other node.  *)

  let do_scc t =
    let state = { sccs = []; table = Hashtbl.create (module Node); leaf_sccs = [] } in
    (* The stack used to record which nodes belong to the current SCC *)
    let scc_stack = Stack.create () in
    (* Allocates and initialises fresh node data.  *)
    let create_data =
      let next_idx = ref 0 in
      fun () ->
        let idx = post_incr next_idx in
        { idx
        ; low_idx = idx
        ; stacked = false
        ; scc_id = -1
        ; contains_outside_edge = false
        }
    in
    (* Pop the scc stack until a node with [idx] is reached. Return the [scc]. 
       Update each node data with the [scc_id] *)
    let pop_scc_stack_until ~idx ~scc_id =
      let rec loop acc is_leaf =
        assert (not (Stack.is_empty scc_stack));
        let data, node = Stack.pop_exn scc_stack in
        data.stacked <- false;
        data.scc_id <- scc_id;
        let acc = node :: acc in
        let is_leaf = is_leaf && not data.contains_outside_edge in
        if data.idx = idx
        then (
          assert (data.idx = data.low_idx);
          acc, is_leaf)
        else loop acc is_leaf
      in
      loop [] true
    in
    let create_scc =
      let next_scc_id = ref 0 in
      fun ~idx ->
        let scc_id = post_incr next_scc_id in
        let scc, is_leaf = pop_scc_stack_until ~idx ~scc_id in
        if is_leaf then state.leaf_sccs <- scc :: state.leaf_sccs;
        state.sccs <- scc :: state.sccs
    in
    let update_min_idx data data' = data.low_idx <- min data.low_idx data'.low_idx in
    let rec visit node =
      [%log.global.debug
        "Visiting" (node : Node.t) (state : state) (scc_stack : (data * Node.t) Stack.t)];
      match Hashtbl.find state.table node with
      | Some _ ->
        [%log.global.debug "Already visited"];
        ()
      | None ->
        [%log.global.debug "Unvisited node"];
        let data = create_data () in
        Hashtbl.set state.table ~key:node ~data;
        Stack.push scc_stack (data, node);
        data.stacked <- true;
        [%log.global.debug "Added to table and stack, visiting children"];
        G.iter_succ t node ~f:(fun succ ->
          [%log.global.debug "Visiting succ" (succ : Node.t)];
          match Hashtbl.find state.table succ with
          | Some data' ->
            [%log.global.debug "Succ previously visited" (data' : data)];
            if data'.stacked
            then update_min_idx data data'
            else
              (* the current node contains an outside edge to a different SCC *)
              data.contains_outside_edge <- true
          | None ->
            [%log.global.debug "Unvisited succ"];
            visit succ;
            let data' = Hashtbl.find_exn state.table succ in
            [%log.global.debug "Finished visiting succ" (data' : data)];
            update_min_idx data data';
            if not data'.stacked then data.contains_outside_edge <- true);
        assert data.stacked;
        if data.idx = data.low_idx
        then (
          [%log.global.debug "Creating scc" (data : data)];
          create_scc ~idx:data.idx)
    in
    G.iter_nodes t ~f:visit;
    assert (Stack.is_empty scc_stack);
    state
  ;;

  let scc t = (do_scc t).sccs

  let scc_leafs t =
    let state = do_scc t in
    [%log.global.debug "Scc state" (state : state)];
    state.leaf_sccs
  ;;
end
