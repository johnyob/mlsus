open Core
open Grace
open Omniml_ast.Ast_types

type t [@@deriving sexp]

exception T of t

val raise : t -> 'a

(** [both t1 t2] combines two errors into one *)
val both : t -> t -> t

(** [all ts] combines all errors in [ts] into one *)
val all : t list -> t

(** [handle_uncaught ~exit f] catches [T err] escaping [f] and 
    prints the error message to stderr.

    Exits with return code 1 if [exit] is [true] and returns [()] otherwise.
    If [use_ansi] is [None], then rendering is dictated by [TERM] and [isatty stderr]. 
    Otherwise, [use_ansi] can override these defaults. *)
val handle_uncaught : ?use_ansi:bool -> exit:bool -> (unit -> unit) -> unit

(** [bug ~here msg] constructs an internal fatal error.
    This error is only to be used to indicate a bug in Omniml. *)
val bug : here:Source_code_position.t -> Diagnostic.Message.t -> t

(** [bugf ~here fmt ...] formats a message and creates an internal fatal error. *)
val bugf : here:Source_code_position.t -> ('a, t) Diagnostic.format -> 'a

val bug_s : here:Source_code_position.t -> Sexp.t -> t
val unterminated_comment : range:Range.t -> t
val unknown_start_of_token : range:Range.t -> char -> t
val syntax_error : range:Range.t -> t
val file_not_found : string -> t
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
  -> type_head:[ `Tuple | `Arrow | `Poly ]
  -> t

val disambiguation_tuple_mismatched_type
  :  range:Range.t
  -> type_head:[ `Constr | `Arrow | `Poly ]
  -> t

val projection_out_of_bounds : range:Range.t -> arity:int -> index:int -> t
val ambiguous_label : range:Range.t -> t
val rigid_variable_escape : range:Range.t -> t
val scheme_mismatched_type : range:Range.t -> type_head:[ `Tuple | `Arrow | `Constr ] -> t

val polytype_mismatched_type
  :  range:Range.t
  -> type_head:[ `Tuple | `Arrow | `Constr | `Poly ]
  -> t

val ambiguous_tuple : range:Range.t -> t
val ambiguous_polytype : range:Range.t -> t
val non_linear_pattern : Var_name.t -> fst_range:Range.t -> snd_range:Range.t -> t
val fcp_disabled : range:Range.t -> t
val cycle : range:Range.t -> pp_type:'a Fmt.t -> 'a -> t
