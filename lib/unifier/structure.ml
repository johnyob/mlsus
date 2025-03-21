(* This module implements signature used for unification structures. *)

module type Basic = sig
  (** A structure defines the internal structure of terms in the unification problem. *)
  type 'a t [@@deriving sexp_of]
end

module type Traverse = sig
  include Basic

  (** [copy t ~f] copies [t] using [f] to copy each child. *)
  val copy : 'a t -> f:('a -> 'a) -> 'a t

  (** [iter t ~f] traverses [t], executing [f] on each child. *)
  val iter : 'a t -> f:('a -> unit) -> unit

  (** [fold t ~f ~init] performs the computation of [f], traversing
      over [t] with the initial accumulator value of [init]. *)
  val fold : 'a t -> f:('a -> 'b -> 'b) -> init:'b -> 'b
end

module type Merge = sig
  include Basic

  (** ['a ctx] represents the arbitrary context used by [merge] *)
  type 'a ctx

  exception Cannot_merge

  (** [merge ~ctx ~create ~unify ~type1 ~type2 t1 t2] computes the
      merged structure of [t1] and [t2]. If the structures are inconsistent, then
      {!Cannot_merge} is raised.

      [merge] can emit first-order equalities using [unify], or create new
      terms from structures using [create], or refer to the types containing the
      structures ([type1] and [type2] for [t1] and [t2] resp.).

      An additional context [ctx] is provided since consistency might
      be contextual. *)
  val merge
    :  ctx:'a ctx
    -> create:('a t -> 'a)
    -> unify:('a -> 'a -> unit)
    -> type1:'a
    -> type2:'a
    -> 'a t
    -> 'a t
    -> 'a t
end

module type S = sig
  include Basic
  include Traverse with type 'a t := 'a t
  include Merge with type 'a t := 'a t
end
