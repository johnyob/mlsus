open Core
open Mlsus_std

module type S = sig
  type 'a structure

  module Type : sig
    (** [t] represents a type *)
    type t [@@deriving sexp_of]

    (** [make structure] creates a new unification type w/ structure [structure]. *)
    val create : t structure -> t

    (** [structure t] returns the structure of [t]. *)
    val structure : t -> t structure

    (** [set_structure t structure] sets the structure of [t] to [structure]. *)
    val set_structure : t -> t structure -> unit

    (** [is_representative t] returns whether [t] is the representative of it's equivalence class. *)
    val is_representative : t -> bool
  end

  module Make_unify (M : Structure.Merge with type 'a t := 'a structure) : sig
    (** [unify ~ctx t1 t2] equates the types [t1] and [t2].

        [Unify (t1, t2)] is raised if the two node cannot be unified. *)

    exception Unify of Type.t * Type.t

    val unify : ctx:Type.t M.ctx -> Type.t -> Type.t -> unit
  end
end

module Make (S : Structure.Basic) = struct
  module Type = struct
    type t = desc Union_find.t [@@deriving sexp_of]
    and desc = { structure : t S.t } [@@unboxed]

    let create structure = Union_find.create { structure }
    let structure t = (Union_find.get t).structure
    let set_structure t structure = Union_find.set t { structure }
    let is_representative t = Union_find.is_root t
  end

  open Type

  module Make_unify (M : Structure.Merge with type 'a t := 'a S.t) = struct
    module Work_queue : sig
      (** A work queue that contains remaining types that must be unified.
          This is required for correctness due to recursive calls to unify the
          same type (e.g. in the case of partial unification). **)
      type t

      val create : unit -> t
      val enqueue : t -> Type.t -> Type.t -> unit
      val run : t -> f:(Type.t -> Type.t -> unit) -> unit
    end = struct
      (* A stack is used since it will likely yield errors earlier. *)
      type t = (Type.t * Type.t) Stack.t

      let create () = Stack.create ()
      let enqueue t type1 type2 = Stack.push t (type1, type2)

      let run t ~f =
        let rec loop () =
          match Stack.pop t with
          | None -> ()
          | Some (type1, type2) ->
            f type1 type2;
            loop ()
        in
        loop ()
      ;;
    end

    let unify_structure ~ctx ~work_queue type1 type2 =
      M.merge
        ~ctx
        ~create:Type.create
        ~unify:(Work_queue.enqueue work_queue)
        ~type1
        ~type2
        (Type.structure type1)
        (Type.structure type2)
    ;;

    let unify_desc ~ctx ~work_queue type1 type2 =
      { structure = unify_structure ~ctx ~work_queue type1 type2 }
    ;;

    let rec unify_exn ~ctx ~work_queue type1 type2 =
      if not (Union_find.same_class type1 type2)
      then (
        let desc = unify_desc ~ctx ~work_queue type1 type2 in
        Union_find.union type1 type2;
        Union_find.set type1 desc);
      Work_queue.run work_queue ~f:(unify_exn ~ctx ~work_queue)
    ;;

    exception Unify of Type.t * Type.t

    let unify ~ctx t1 t2 =
      let work_queue = Work_queue.create () in
      try
        Union_find.Transaction.try_or_rollback ~f:(fun () ->
          unify_exn ~ctx ~work_queue t1 t2)
      with
      | M.Cannot_merge -> raise (Unify (t1, t2))
    ;;
  end
end
