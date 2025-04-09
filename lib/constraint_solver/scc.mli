module Make (G : sig
    type t

    module Node : sig
      type t [@@deriving sexp_of, compare, hash]
    end

    val iter_nodes : t -> f:(Node.t -> unit) -> unit
    val iter_succ : t -> Node.t -> f:(Node.t -> unit) -> unit
  end) : sig
  val scc : G.t -> G.Node.t list list
  val scc_leafs : G.t -> G.Node.t list list
end
