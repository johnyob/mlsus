open Core
open Grace
open Mlsus_ast

module Token : sig
  type t [@@deriving to_string]

  include Pretty_printer.S with type t := t

  val is_eof : t -> bool
end

module Lexer : sig
  (** [read_token ?source lexbuf] reads a token from the buffer [lexbuf]

      @param source sets the source used for token ranges
      @raise Mlsus_error.T *)
  val read_token : ?source:Source.t -> Lexing.lexbuf -> Token.t

  (** [read_tokens ?source ?keep_eof lexbuf] reads all tokens from the buffer [lexbuf]

      @param source sets the source used for token ranges
      @param keep_eof if [true] the resultant token list ends with the EOF token
      @raise Mlsus_error.T *)
  val read_tokens : ?source:Source.t -> ?keep_eof:bool -> Lexing.lexbuf -> Token.t list
end

module Parser : sig
  type 'a t = ?source:Source.t -> Lexing.lexbuf -> 'a

  val parse_core_type : Ast.core_type t
  val parse_expression : Ast.expression t
  val parse_structure : Ast.structure t
end
