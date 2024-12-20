open Core
open Ast_types

(* This module defines the type for the abstract syntax tree (AST) produced by
   parsing mlsus's source code. *)

type core_type = core_type_desc with_range [@@deriving sexp_of]

and core_type_desc =
  | Type_var of type_variable_name
  | Type_arrow of core_type * core_type
  | Type_tuple of core_type list
  | Type_constr of core_type list * type_name
[@@deriving sexp_of]

type core_scheme = (string list * core_type) with_range [@@deriving sexp_of]

type pattern = pattern_desc with_range [@@deriving sexp_of]

and pattern_desc =
  | Pat_any
  | Pat_var of variable_name
  | Pat_alias of pattern * variable_name
  | Pat_const of constant
  | Pat_tuple of pattern list
  | Pat_constructor of constructor_name * pattern option
  | Pat_annot of pattern * core_type
[@@deriving sexp_of]

type expression = expression_desc with_range [@@deriving sexp_of]

and expression_desc =
  | Exp_var of variable_name
  | Exp_const of constant
  | Exp_fun of pattern * expression
  | Exp_app of expression * expression
  | Exp_let of rec_flag * value_binding list * expression
  | Exp_exists of type_variable_name list * expression
  | Exp_annot of expression * core_type
  | Exp_constructor of constructor_name * expression option
  | Exp_record of (label_name * expression) list
  | Exp_field of expression * label_name
  | Exp_tuple of expression list
  | Exp_match of expression * case list
  | Exp_if_then_else of expression * expression * expression
  | Exp_sequence of expression * expression
[@@deriving sexp_of]

and value_binding = value_binding_desc with_range [@@deriving sexp_of]

and value_binding_desc =
  { value_binding_pat : pattern
  ; value_binding_exp : expression
  }
[@@deriving sexp_of]

and case = case_desc with_range [@@deriving sexp_of]

and case_desc =
  { case_lhs : pattern
  ; case_rhs : expression
  }
[@@deriving sexp_of]

type value_description = value_description_desc with_range [@@deriving sexp_of]

and value_description_desc =
  { value_name : variable_name
  ; value_type : core_scheme
  }
[@@deriving sexp_of]

type type_declaration = type_description_desc with_range [@@deriving sexp_of]

and type_description_desc =
  { type_decl_name : type_name
  ; type_decl_params : type_variable_name list
  ; type_decl_kind : type_decl_kind
  }
[@@deriving sexp_of]

and type_decl_kind =
  | Type_decl_variant of constructor_declaration list
  | Type_decl_record of label_declaration list
  | Type_decl_abstract

and label_declaration =
  { label_name : label_name
  ; label_arg : core_type
  }
[@@deriving sexp_of]

and constructor_declaration =
  { constructor_name : constructor_name
  ; constructor_arg : core_type option
  }
[@@deriving sexp_of]

type structure_item = structure_item_desc with_range [@@deriving sexp_of]

and structure_item_desc =
  | Str_value of rec_flag * value_binding list
  | Str_primitive of value_description
  | Str_type of type_declaration list
[@@deriving sexp_of]

type structure = structure_item list [@@deriving sexp_of]
