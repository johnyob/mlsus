open Base

(* This module implements an imperative data structure for disjoint sets
   (commonly known as `union-find'), based on Tarjan and Huet.

   Union find implements a family of disjoint sets on values, where
   the disjoint sets can dynamically be combined using [union].

   A disjoint set [D] is a family of disjoint sets [D = {t1, ..., tn}],
   with the following operations:
   - [create v]: creates a new set [t] containing [v] in [D].
   - [find v] returns the (unique) set [t] in [D] that contains [v].
   - [union t1 t2] performs the union of [t1] and [t2] in [D].

   A disjoint set [D] is represeted using a forest, a collection of trees,
   each node in the tree storing it's value, with pointers to parents.

   Operations:
   - [find v]:
     This traverses the element [v] back to the root [r] of the set,
     creating a path [p] (the `find' path).

   Path compression is performed on this operation, which updates the
   parent pointer to point directly to the root [r].

   - [union t1 t2]:
     We use union by rank. Each set stores the `rank', an upper bound for the
     height of the tree. The set with the smallest rank becomes the child,
     with the edge case of equal ranks.

   This implementation is optimized for the representation of equivalent
   classes. Each equivalence class containing a "value".
*)

module Transactional_store = struct
  module Ref = struct
    type 'a t =
      { mutable contents : 'a (** The current (uncommitted) value *)
      ; mutable committed_contents : 'a (** The last committed value *)
      }
    [@@deriving sexp]

    type packed = Packed : 'a t -> packed [@@deriving sexp_of]

    let create contents = { contents; committed_contents = contents }
    let equal = phys_equal
  end

  type t = { mutable transaction : transaction option }
  and transaction = Ref.packed Stack.t [@@deriving sexp_of]

  let t = { transaction = None }
  let get (ref : _ Ref.t) = ref.contents

  let set (ref : 'a Ref.t) (value : 'a) =
    if phys_equal ref.contents value
    then ()
    else (
      match t.transaction with
      | None ->
        ref.contents <- value;
        ref.committed_contents <- value
      | Some tx ->
        if phys_equal ref.contents ref.committed_contents then Stack.push tx (Packed ref);
        ref.contents <- value)
  ;;

  let commit_ref (Ref.Packed ref) = ref.committed_contents <- ref.contents
  let rollback_ref (Ref.Packed ref) = ref.contents <- ref.committed_contents

  let try_or_rollback ~f =
    match t.transaction with
    | Some _ -> raise_s [%message "Cannot nest transactions"]
    | None ->
      let tx = Stack.create () in
      t.transaction <- Some tx;
      (try
         let result = f () in
         Stack.iter tx ~f:commit_ref;
         t.transaction <- None;
         result
       with
       | exn ->
         let bt = Backtrace.get () in
         Stack.iter tx ~f:rollback_ref;
         t.transaction <- None;
         Exn.raise_with_original_backtrace exn bt)
  ;;
end

(* Trees representing equivalence classes are of the form:
   {v
            Root
             |
           Inner
        / .. | .. \
     Inner Inner Inner
      /|\   /|\   /|\
      ...   ...   ...
   v}

   With directed edges towards the parents.
   The root of the class contains the [rank] and value of type ['a].
   Internal nodes contain a pointer to their parent.
*)

type 'a root =
  { rank : int
  ; value : 'a
  }

and 'a node =
  | Root of 'a root
  | Inner of 'a t

and 'a t = 'a node Transactional_store.Ref.t [@@deriving sexp_of]

let invariant _ t =
  let rec loop t height =
    match Transactional_store.get t with
    | Root r -> assert (height <= r.rank)
    | Inner t -> loop t (height + 1)
  in
  loop t 0
;;

let create v = Transactional_store.Ref.create (Root { rank = 0; value = v })

(* [compress t ~imm_desc ~imm_desc_node ~prop_descs] compresses the path
   from [t] upwards to the root of [t]'s tree, where:
   - [imm_desc] is the immediate descendent of [t], and
   - [prop_descs] are proper descendents of [imm_desc]

   The use of [imm_desc_node] is to avoid additional heap allocation
   when performing path compression.
*)
let rec compress t ~imm_desc ~imm_desc_node ~prop_descs =
  match Transactional_store.get t with
  | Root r ->
    (* Perform path compression *)
    List.iter prop_descs ~f:(fun t -> Transactional_store.set t imm_desc_node);
    (* Return pointer to root and it's contents *)
    t, r
  | Inner t' as imm_desc_node ->
    compress t' ~imm_desc:t ~imm_desc_node ~prop_descs:(imm_desc :: prop_descs)
;;

let repr t =
  match Transactional_store.get t with
  | Root r -> t, r
  | Inner t' as imm_desc_node -> compress t' ~imm_desc:t ~imm_desc_node ~prop_descs:[]
;;

let root t =
  match Transactional_store.get t with
  | Root r -> r
  | _ -> snd (repr t)
;;

let get t = (root t).value

let set t v =
  let t, root = repr t in
  Transactional_store.set t (Root { root with value = v })
;;

let union t1 t2 =
  let t1, r1 = repr t1 in
  let t2, r2 = repr t2 in
  if Transactional_store.Ref.equal t1 t2
  then ()
  else (
    let n1 = r1.rank in
    let n2 = r2.rank in
    if n1 < n2
    then Transactional_store.set t1 (Inner t2)
    else (
      Transactional_store.set t2 (Inner t1);
      if n1 = n2 then Transactional_store.set t1 (Root { r1 with rank = r1.rank + 1 })))
;;

let same_class t1 t2 = Transactional_store.Ref.equal (root t1) (root t2)

let is_root t =
  match Transactional_store.get t with
  | Root _ -> true
  | Inner _ -> false
;;

module Transaction = struct
  let try_or_rollback = Transactional_store.try_or_rollback
end
