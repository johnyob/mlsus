open Grace

(** [lex_and_print lexbuf] reads the tokens in [lexbuf] and prints them.
    Any errors are additionally printed. *)
val lex_and_print : Lexing.lexbuf -> unit

(** [parse_and_print lexbuf] parses the [lexbuf] as a structure and prints it.
    Any errors are additionally printed. *)
val parse_and_print : ?source:Source.t -> Lexing.lexbuf -> unit

(** [constraint_gen_and_print lexbuf ~dump_ast] parses the [lexbuf] as a structure,
    generates a well-typedness constraint, and then prints it.

    If [dump_ast] is [true], then the parsed structure is printed.
    Any errors are additionally printed. *)
val constraint_gen_and_print : ?source:Source.t -> Lexing.lexbuf -> dump_ast:bool -> unit

(** [type_check_and_print lexbuf ~dump_ast ~dump_constraint] parses the [lexbuf] as a structure,
    generates a well-typedness constraint, solves the constraint and prints the result.

    If [dump_ast] is [true], then the parsed structure is printed.
    If [dump_constraint] is [true], then the generated constraint is printed.
    Any errors are additionally printed. *)
val type_check_and_print
  :  ?source:Source.t
  -> Lexing.lexbuf
  -> dump_ast:bool
  -> dump_constraint:bool
  -> unit
