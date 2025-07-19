open Core
open Grace
open Mlsus_ast.Ast_types

type t [@@deriving sexp]

exception T of t

val raise : t -> 'a

include Pretty_printer.S with type t := t

(** [handle_uncaught ~exit f] catches [T err] escaping [f] and prints the error
    message to stderr.

    Exits with return code 1 if [exit] is [true] and [f] is not running
    in an expect test, and returns unit otherwise. *)
val handle_uncaught : exit:bool -> (unit -> unit) -> unit

(** [bug ~here msg] constructs an internal fatal error.
    This error is only to be used to indicate a bug in Mlsus. *)
val bug : here:Source_code_position.t -> Diagnostic.Message.t -> t

(** [bugf ~here fmt ...] formats a message and creates an internal fatal error. *)
val bugf : here:Source_code_position.t -> ('a, t) Diagnostic.format -> 'a

val bug_s : here:Source_code_position.t -> Sexp.t -> t
val unterminated_comment : range:Range.t -> t
val unknown_start_of_token : range:Range.t -> char -> t
val syntax_error : range:Range.t -> t
val unbound_variable : range:Range.t -> Var_name.t -> t
val unbound_type : range:Range.t -> Type_name.t -> t
val unbound_type_variable : range:Range.t -> Type_var_name.t -> t
val unbound_constructor : range:Range.t -> Constructor_name.t -> t
val unbound_label : range:Range.t -> Label_name.t -> t

val type_constructor_arity_mismatch
  :  args_range:Range.t
  -> actual_arity:int
  -> expected_arity:int
  -> Type_name.With_range.t
  -> t

val constructor_arity_mismatch
  :  arg_range:Range.t
  -> actual_arity:[< `Zero | `One ]
  -> expected_arity:[< `Zero | `One ]
  -> Constructor_name.With_range.t
  -> t

(** [mismatched_type ~range ~pp_type type1 type2] creates a type mismatch
    error. The parameterization of types permits us to use many different
    representations for output types.

    @param pp_type is used to pretty-print the types. *)
val mismatched_type : range:Range.t -> pp_type:'a Fmt.t -> 'a -> 'a -> t

val ambiguous_constructor : range:Range.t -> t

val disambiguation_mismatched_type
  :  range:Range.t
  -> type_head:[ `Tuple | `Arrow | `Rigid_var ]
  -> t

val disambiguation_tuple_mismatched_type
  :  range:Range.t
  -> type_head:[ `Constr | `Arrow | `Rigid_var ]
  -> t

val projection_out_of_bounds : range:Range.t -> arity:int -> index:int -> t
val ambiguous_label : range:Range.t -> t
val rigid_variable_escape : range:Range.t -> t

module For_testing : sig
  val use_expect_test_config : unit -> unit
end
