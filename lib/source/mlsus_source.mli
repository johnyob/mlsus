open Grace

(** [with_source src f] runs [f] with the current source set to [src],
    clearing it once [f] returns. *)
val with_source : source:Source.t -> (unit -> 'a) -> 'a

(** [with_optional_source] optionally sets the source and runs [f]. *)
val with_optional_source : ?source:Source.t -> (unit -> 'a) -> 'a

(** [get ()] returns the current source.
    Returns [None] if no source is set. *)
val get : unit -> Source.t option

(** [get_exn ()] returns the current source. *)
val get_exn : unit -> Source.t

module For_testing : sig
  val expect_test_source : string -> Source.t
end
