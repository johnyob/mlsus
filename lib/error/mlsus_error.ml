open Core
open Grace
open Mlsus_ast.Ast_types

let is_in_expect_test = ref false

module Code = struct
  type t =
    | Unterminated_comment
    | Unknown_start_of_token
    | Syntax_error
    | Unbound_variable
    | Unbound_type_name
    | Unbound_type_variable
    | Unbound_constructor
    | Type_constructor_arity_mismatch
    | Constructor_arity_mismatch
    | Ambiguous_constructor
    | Type_mismatch
    | Rigid_variable_escape
    | Ambiguous_label
    | Projection_out_of_bounds
    | Unknown
  [@@deriving sexp]

  let to_string = function
    | Unterminated_comment -> "E001"
    | Unknown_start_of_token -> "E002"
    | Syntax_error -> "E003"
    | Unbound_variable -> "E004"
    | Unbound_type_name -> "E005"
    | Unbound_type_variable -> "E006"
    | Unbound_constructor -> "E007"
    | Type_constructor_arity_mismatch -> "E008"
    | Constructor_arity_mismatch -> "E009"
    | Ambiguous_constructor -> "E010"
    | Type_mismatch -> "E011"
    | Rigid_variable_escape -> "E012"
    | Ambiguous_label -> "E013"
    | Projection_out_of_bounds -> "E014"
    | Unknown -> "E???"
  ;;
end

type t = Code.t Diagnostic.t [@@deriving sexp]

exception T of t

let raise t = raise (T t) [@@always_inline]

let pp ppf t =
  let open Grace_ansi_renderer in
  let config = { Config.default with use_ansi = not !is_in_expect_test } in
  Grace_ansi_renderer.pp_diagnostic ~config ~code_to_string:Code.to_string () ppf t
;;

let handle_uncaught ~exit:should_exit f =
  try f () with
  | T err ->
    Fmt.(pf stderr "@[%a@]@." pp err);
    if should_exit && not !is_in_expect_test then exit 1
;;

(* Constructors for errors *)

let pp_quoted pp ppf x = Fmt.pf ppf "`%a`" pp x
let pp_quoted_s = pp_quoted Fmt.string

let pp_type_var_name ppf (type_var : Type_var_name.t) =
  Fmt.pf ppf "'%s" (type_var :> string)
;;

let empty_primary_label ~range = Diagnostic.Label.primaryf ~range ""

let bug ~here msg =
  Diagnostic.(
    create
      ~code:Code.Unknown
      Bug
      (Message.createf "%s: %a" (Source_code_position.to_string here) Message.pp msg))
;;

let bugf ~here fmt = fmt |> Diagnostic.Message.kcreatef (bug ~here)
let bug_s ~here sexp = bugf ~here "%a" Sexp.pp_hum sexp

let unterminated_comment ~range : t =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Unterminated_comment
    Error
    "unterminated comment"
;;

let unknown_start_of_token ~range c : t =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Unknown_start_of_token
    Error
    "unknown start of token: %C"
    c
;;

let syntax_error ~range : t =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Syntax_error
    Error
    "syntax error"
;;

let not_found_in_this_scope_label ~range =
  Diagnostic.Label.primaryf ~range "not found in this scope"
;;

let unbound_variable ~range (var_name : Var_name.t) : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_variable
    Error
    "cannot find value %a in this scope"
    pp_quoted_s
    (var_name :> string)
;;

let unbound_type ~range (type_name : Type_name.t) : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_type_name
    Error
    "cannot find type %a in this scope"
    pp_quoted_s
    (type_name :> string)
;;

let unbound_type_variable ~range type_var : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_type_variable
    Error
    "cannot find type variable %a in this scope"
    (pp_quoted pp_type_var_name)
    type_var
;;

let unbound_constructor ~range (constr_name : Constructor_name.t) : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_constructor
    Error
    "cannot find constructor %a in this scope"
    pp_quoted_s
    (constr_name :> string)
;;

let unbound_label ~range (label_name : Label_name.t) : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_constructor
    Error
    "cannot find label %a in this scope"
    pp_quoted_s
    (label_name :> string)
;;

let type_constructor_arity_mismatch
      ~args_range
      ~actual_arity
      ~expected_arity
      (type_name : Type_name.With_range.t)
  : t
  =
  let open Diagnostic in
  assert (actual_arity <> expected_arity);
  let expected_arguments_label =
    Label.primaryf ~range:type_name.range "expected %d arguments" expected_arity
  in
  if actual_arity = 0
  then
    Diagnostic.createf
      ~labels:[ expected_arguments_label ]
      ~code:Code.Type_constructor_arity_mismatch
      Error
      "missing type arguments for type %a"
      pp_quoted_s
      (type_name.it :> string)
  else
    Diagnostic.createf
      ~labels:
        [ expected_arguments_label
        ; Label.secondary
            ~range:args_range
            (if actual_arity > expected_arity
             then Message.create "help: remove the unnecessary arguments"
             else Message.createf "supplied %d arguments" actual_arity)
        ]
      ~code:Code.Type_constructor_arity_mismatch
      Error
      "type takes %d arguments but %d arguments were supplied"
      expected_arity
      actual_arity
;;

let constructor_arity_mismatch
      ~arg_range
      ~actual_arity
      ~expected_arity
      (constr_name : Constructor_name.With_range.t)
  =
  let open Diagnostic in
  let expected_arguments_label expected_arity =
    Label.primaryf ~range:constr_name.range "expected %d arguments" expected_arity
  in
  match actual_arity, expected_arity with
  | `One, `Zero ->
    Diagnostic.createf
      ~labels:
        [ expected_arguments_label 0
        ; Label.secondary
            ~range:arg_range
            (Message.create "help: remove the unnecessary argument")
        ]
      ~code:Code.Constructor_arity_mismatch
      Error
      "too many arguments for constructor %a"
      pp_quoted_s
      (constr_name.it :> string)
  | `Zero, `One ->
    Diagnostic.createf
      ~labels:
        [ expected_arguments_label 1
        ; Label.secondary ~range:arg_range (Message.create "supplied 0 arguments")
        ]
      ~code:Code.Constructor_arity_mismatch
      Error
      "too few arguments for constructor %a"
      pp_quoted_s
      (constr_name.it :> string)
  | `One, `One | `Zero, `Zero ->
    raise @@ bugf ~here:[%here] "expected actual_arity <> expected_arity"
;;

let mismatched_type ~range ~pp_type type1 type2 =
  let open Diagnostic in
  let pp_quoted_type = pp_quoted pp_type in
  Diagnostic.createf
    ~labels:
      [ Label.primaryf
          ~range
          "%a is not equal to %a"
          pp_quoted_type
          type1
          pp_quoted_type
          type2
      ]
    ~code:Code.Type_mismatch
    Error
    "mismatched type"
;;

let disambiguation_mismatched_type ~range ~type_head =
  let open Diagnostic in
  let head_name =
    match type_head with
    | `Tuple -> "tuple"
    | `Arrow -> "function type"
    | `Rigid_var -> "polymorphic variable"
  in
  Diagnostic.createf
    ~labels:[ Label.primaryf ~range "expected a type constructor, found a %s" head_name ]
    ~code:Code.Type_mismatch
    Error
    "mismatched type"
;;

let projection_out_of_bounds ~range ~arity ~index =
  let open Diagnostic in
  Diagnostic.createf
    ~labels:[ Label.primaryf ~range "unknown field" ]
    ~code:Code.Projection_out_of_bounds
    Error
    "no field %a in tuple of arity %d"
    (pp_quoted Fmt.int)
    index
    arity
;;

let disambiguation_tuple_mismatched_type ~range ~type_head =
  let open Diagnostic in
  let head_name =
    match type_head with
    | `Constr -> "type constructor"
    | `Arrow -> "function type"
    | `Rigid_var -> "polymorphic variable"
  in
  Diagnostic.createf
    ~labels:[ Label.primaryf ~range "expected a tuple, found a %s" head_name ]
    ~code:Code.Type_mismatch
    Error
    "mismatched type"
;;

let ambiguous_constructor ~range =
  let open Diagnostic in
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~notes:[ Message.createf "hint: add a type annotation" ]
    ~code:Code.Ambiguous_constructor
    Error
    "ambiguous constructor"
;;

let rigid_variable_escape ~range =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Rigid_variable_escape
    Error
    "generic type variable escapes its scope"
;;

let ambiguous_label ~range =
  let open Diagnostic in
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~notes:[ Message.createf "hint: add a type annotation" ]
    ~code:Code.Ambiguous_label
    Error
    "ambiguous label"
;;

module For_testing = struct
  let use_expect_test_config () = is_in_expect_test := true
end
