open! Import
open Ast_types
module Type_ident = Constraint.Type.Ident

module Constructor_ident = Var.Make (struct
    let module_name = "Adt.Constructor_name"
  end)

type type_expr =
  | Type_var of Type_var_name.t
  | Type_arrow of type_expr * type_expr
  | Type_tuple of type_expr list
  | Type_constr of type_expr list * Type_ident.t
  | Type_poly of type_scheme_expr

and type_scheme_expr =
  { scheme_quantifiers : Type_var_name.t list
  ; scheme_body : type_expr
  }
[@@deriving sexp_of]

(** Type definitions to encode user-defined types e.g. variants. *)

type type_definition =
  { type_name : Type_name.t (** The user-defined name of the type that is declared. *)
  ; type_ident : Type_ident.t (** The unique name of the type. *)
  ; type_arity : int (** The number of type parameters of the type. *)
  ; type_kind : type_def_kind (** The kind of the type declaration. *)
  }
[@@deriving sexp_of]

and type_def_kind =
  | Type_variant of constructor_definition list
  | Type_record of label_definition list
  | Type_abstract
[@@deriving sexp_of]

and constructor_definition =
  { constructor_name : Constructor_name.t (** The user-defined name of the constructor. *)
  ; constructor_alphas : Type_var_name.t list
  ; constructor_arg : type_expr option
  ; constructor_type : type_expr
  ; constructor_type_ident : Type_ident.t
  }

and constructor_arity =
  | Zero
  | One

and label_definition =
  { label_name : Label_name.t
  ; label_alphas : Type_var_name.t list
  ; label_arg : type_expr
  ; label_type : type_expr
  ; label_type_ident : Type_ident.t
  }
[@@deriving sexp_of]
