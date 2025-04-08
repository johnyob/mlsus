open! Import
open Ast_types
open Adt

type t

(** [empty ?id_source ()] returns an empty environment.

    If provided, [id_source] permits re-using an existing source instead of
    creating a new one. *)
val empty : ?id_source:Identifier.source -> unit -> t

(** [id_source t] returns the identifier source associated with the environment [t] *)
val id_source : t -> Identifier.source

(** [define_type t ~type_name ~type_arity ~in_] declares [type_name] with arity
    [type_arity] and a fresh [type_ident] in [in_]. *)
val declare_type
  :  t
  -> type_name:Type_name.t
  -> type_arity:int
  -> in_:(t -> Type_ident.t -> 'a)
  -> 'a

val declare_types
  :  t
  -> (Type_name.t * int) list
  -> in_:(t -> Type_ident.t list -> 'a)
  -> 'a

(** [add_type_def t td] adds the type definition [td] to the environment [t]. *)
val add_type_def : t -> type_definition -> t

(** [find_constr t constr_name] returns a list of constructor declarations with
    the name [constr_name]. If no constructor declarations with [constr_name] exist,
    then the empty list is returned. *)
val find_constr : t -> Constructor_name.t -> constructor_definition list

(** [find_label t label_name] returns a list of label definitions with
    the name [label_name]. If no label definitions with [label_name] exist,
    then the empty list is returned. *)
val find_label : t -> Label_name.t -> label_definition list

(** [find_type_def t type_name] returns a list of type definitions with the
    name [type_name]. If no type definition with [type_name] exist, then the
    empty list is returned. *)
val find_type_def : t -> Type_name.t -> type_definition list

(** [find_var t var_name] returns the constraint variable that [var_name] is renamed to. *)
val find_var : t -> Var_name.t -> Constraint.Var.t option

(** [rename_var t ~var ~in_] renames the variable [var] to some fresh [cvar] in [in_]. *)
val rename_var : t -> var:Var_name.t -> in_:(t -> Constraint.Var.t -> 'a) -> 'a

(** [find_type_var t type_var_name] returns the type variable that [type_var_name]
    is renamed to. *)
val find_type_var : t -> Type_var_name.t -> Constraint.Type.Var.t option

(** [rename_type_var t ~type_var ~in_] renames the type variable [type_var] to some fresh
    [ctype_var] in [in_]. *)
val rename_type_var
  :  t
  -> type_var:Type_var_name.t
  -> in_:(t -> Constraint.Type.Var.t -> 'a)
  -> 'a
