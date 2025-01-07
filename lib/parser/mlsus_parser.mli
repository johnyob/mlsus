open Core
open Grace
open Mlsus_ast

module Token : sig
  type t [@@deriving to_string]

  include Pretty_printer.S with type t := t

  val is_eof : t -> bool
end

module Lexer : sig
  module Error : sig
    type t = [ `Lexer_error of string ]

    include Pretty_printer.S with type t := t
  end

  val read_token : Lexing.lexbuf -> (Token.t, [> Error.t ]) result
  val read_tokens : ?keep_eof:bool -> Lexing.lexbuf -> (Token.t list, [> Error.t ]) result
end

module Parser : sig
  module Error : sig
    type t =
      [ Lexer.Error.t
      | `Parser_error
      ]

    include Pretty_printer.S with type t := t
  end

  type ('a, 'err) t =
    ?source:Source.t -> Lexing.lexbuf -> ('a, ([> Error.t ] as 'err)) result

  val parse_core_type : (Ast.core_type, 'err) t
  val parse_expression : (Ast.expression, 'err) t
  val parse_structure : (Ast.structure, 'err) t
end
