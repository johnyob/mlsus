%{
open Grace
open Mlsus_ast 
open Ast_types
open Ast_builder.Default

(* A set of predefined operator names *)
module Predef_names = struct 
  let or_ ~range = var_name ~range "( || )"
  let and_ ~range = var_name ~range "( && )"

  let equal ~range = var_name ~range "( = )"
  let not_equal ~range = var_name ~range "( <> )"
  let less_than ~range = var_name ~range "( < )"
  let greater_than ~range = var_name ~range "( > )"
  let less_than_equal ~range = var_name ~range "( <= )"
  let greater_than_equal ~range = var_name ~range "( >= )"
  
  let add ~range = var_name ~range "( + )"
  let sub ~range = var_name ~range "( - )"
  let mul ~range = var_name ~range "( * )"
  let div ~range = var_name ~range "( / )" 
  
  let neg ~range = var_name ~range "unary( - )"
end 

let binary_op ~range ~op ~exp1 ~exp2 =
  Expression.(app ~range (app ~range (var ~range op) exp1) exp2)

let unary_op ~range ~op ~exp = 
  Expression.(app ~range (var ~range op) exp)

let range_of_lex lex = 
  Range.of_lex ?source:(Mlsus_source.get ()) lex
%}

%nonassoc prec_below_SEMI
%nonassoc ";"

%left "||"
%left "&&"
%left "=" "<>" "<" "<=" ">" ">="
%left "+" "-"
%left "*" "/" 
%nonassoc prec_unary_op

%start  parse_core_type parse_expression parse_structure
%type <Ast.structure> parse_structure
%type <Ast.expression> parse_expression
%type <Ast.core_type> parse_core_type

%%

(** {1 Start Symbols} *)

parse_structure:
  str = structure; EOF 
    { str }

parse_expression:
  exp = expression; EOF 
    { exp }

parse_core_type:
  type_ = core_type; EOF 
    { type_ }

(** {2 Standard Library Extensions} 

    This section contains definitions of several generic parameterized rules that 
    are useful for parsing mlsus. *)

(** [seperated_nontrivial_list(sep, X)] parases a list containing at least two [X]s 
    separated by [sep]. *)
separated_nontrivial_list(sep, X):
    x1 = X
    ; sep
    ; x2 = X
      { [ x1; x2 ] }
  | x = X
    ; sep
    ; xs = separated_nontrivial_list(sep, X)
      { x :: xs }

(** [preceded_or_separated_nonempty_list(sep, X)] parses a non-emppty list of [X]s separated 
    by [sep], optionally preceded by [sep]. *)
%inline preceded_or_separated_nonempty_list(sep, X):
  ioption(sep); xs = separated_nonempty_list(sep, X)
    { xs }


(** {3 Core Types} 

    This section contains the rules for parsing the grammar of core types:
    {v
      tau ::=   
        | 'a                (* variables *) 
        | tau -> tau        (* functions *)
        | tau * ... * tau   (* tuples *)
        | overline(tau) T   (* type constructors *)
    v} 
    
    The grammar is {e stratified} to handle the precedence issues that arise. *)

type_var_name:
  "'"; id = "<ident>"
    { type_var_name ~range:(range_of_lex $loc) id }

type_name:
  id = "<ident>"
    { type_name ~range:(range_of_lex $loc) id }

%inline core_type:
  type_ = arrow_type
    { type_ }

arrow_type:
    type_ = tuple_type
      { type_ }   
  | type1 = tuple_type
    ; "->"
    ; type2 = core_type
      { Type.arrow ~range:(range_of_lex $loc) type1 type2 }

tuple_type:
    type_ = atom_type
      { type_ }
  | types = separated_nontrivial_list("*", atom_type)
      { Type.tuple ~range:(range_of_lex $loc) types }

atom_type:
    "("
    ; type_ = core_type
    ; ")"
      { type_ }
  | type_var_name = type_var_name
      { Type.var ~range:(range_of_lex $loc) type_var_name }
  | arg_types = type_argument_list
    ; type_name = type_name
      { Type.constr ~range:(range_of_lex $loc) arg_types type_name }

%inline type_argument_list:
    (* empty *)   
      { [] }
  | type_ = atom_type 
      { [ type_ ] }
  | "("
    ; types = separated_nontrivial_list(",", core_type)
    ; ")"
      { types }


(** {4 Expressions and Patterns} 

    This section contains the rules for parsing the grammar of expressions
    {v
      e ::= 
        | x                                 (* variable *)
        | const                             (* constants *)
        | uop e                             (* unary operator *)
        | e bop e                           (* binary operator *)
        | if e then e else e                (* if-then-else *)
        | fun overline(p) -> e              (* functions *)
        | e e                               (* function application *)
        | exists (type overline('a)) -> e   (* type exists binder *)
        | match e with ( overline(c) )      (* match *)
        | let vb in e                       (* let *)
        | { l1 = e1; ...; ln = en }         (* record *)
        | (e1, ..., en)                     (* tuples *)
        | K e?                              (* constructor *)
        | e.l                               (* field *)
        | e; e                              (* sequence *)
        | (e : tau)                         (* type annotation *)
    v} 

    Expressions also include cases, patterns and value bindings, given by the following 
    grammars:
    {v
      p ::= 
        | x 
        | _
        | p as x 
        | K p?
        | { l1 = p1; ...; ln = pn }
        | (p1, ..., pn)
        | (p : tau)

      c ::= p -> e 

      vb ::= p = e
    v}
*)

%inline var_name:
  id = "<ident>"
    { var_name ~range:(range_of_lex $loc) id }

%inline constr_name:
  uid = "<upper_ident>"
    { constr_name ~range:(range_of_lex $loc) uid }

%inline label_name:
  id = "<ident>"
    { label_name ~range:(range_of_lex $loc) id }

constant:
    int = "<int>"
      { Const_int int }
  | "true"
      { Const_bool true }
  | "false"
      { Const_bool false }
  | "()"
      { Const_unit }

seq_expression:
    exp = expression %prec prec_below_SEMI     
      { exp }
  | exp1 = expression
    ; ";"
    ; exp2 = seq_expression
      { Expression.sequence ~range:(range_of_lex $loc) exp1 exp2 }

expression:
    exp = app_expression                                                                   
      { exp }
  | op = unary_op
    ; exp = expression %prec prec_unary_op
      { unary_op ~range:(range_of_lex $loc) ~op ~exp }
  | exp1 = expression
    ; op = bin_op
    ; exp2 = expression
      { binary_op ~range:(range_of_lex $loc) ~op ~exp1 ~exp2 }
  | "if"
    ; cond = expression
    ; "then"
    ; then_ = seq_expression
    ; "else"
    ; else_ = seq_expression
      { Expression.if_ ~range:(range_of_lex $loc) cond ~then_ ~else_ }
  | "fun"
    ; pats = nonempty_list(atom_pattern)
    ; "->"
    ; exp = seq_expression 
      { Expression.fun_ ~range:(range_of_lex $loc) pats exp }
  | "exists"
    ; "("
    ; "type"
    ; type_var_names = nonempty_list(type_var_name)
    ; ")"
    ; "->"
    ; exp = seq_expression
      { Expression.exists ~range:(range_of_lex $loc) type_var_names exp }
  | "forall"
    ; "("
    ; "type"
    ; type_var_names = nonempty_list(type_var_name)
    ; ")"
    ; "->"
    ; exp = seq_expression
        { Expression.forall ~range:(range_of_lex $loc) type_var_names exp }
  | "match" 
    ; exp = expression 
    ; "with" 
    ; cases = cases
      { Expression.match_ ~range:(range_of_lex $loc) exp ~with_:cases }
  | "let"
    ; value_binding = value_binding
    ; "in"
    ; exp = seq_expression
      { Expression.let_ ~range:(range_of_lex $loc) value_binding ~in_:exp }

app_expression:
    exp = atom_expression
      { exp }
  | constr_name = constr_name 
    ; arg_exp = atom_expression
      { Expression.constr ~range:(range_of_lex $loc) constr_name (Some arg_exp) }
  | exp1 = app_expression
    ; exp2 = atom_expression
      { Expression.app ~range:(range_of_lex $loc) exp1 exp2 }

value_binding:
  var_name = var_name 
  ; "="
  ; exp = seq_expression
    { value_binding ~range:(range_of_lex $loc) var_name exp }

cases:
  "("
  ; cases = preceded_or_separated_nonempty_list("|", case)
  ; ")"
    { cases }

case:
  pat = pattern
  ; "->"
  ; exp = seq_expression
    { Expression.case ~range:(range_of_lex $loc) ~lhs:pat ~rhs:exp }

record_assignment(X):
  label_name = label_name
  ; "="
  ; x = X 
    { (label_name, x) }    

atom_expression:
    const = constant 
      { Expression.const ~range:(range_of_lex $loc) const }
  | var_name = var_name
      { Expression.var ~range:(range_of_lex $loc) var_name }
  | constr_name = constr_name
      { Expression.constr ~range:(range_of_lex $loc) constr_name None }
  | "("
    ; exps = separated_nontrivial_list(",", seq_expression)
    ; ")"
      { Expression.tuple ~range:(range_of_lex $loc) exps }
  | "{" 
    ; label_exps = separated_nonempty_list(";", record_assignment(expression))
    ; "}"
      { Expression.record ~range:(range_of_lex $loc) label_exps }
  | exp = atom_expression 
    ; "."  
    ; label_name = label_name
      { Expression.field ~range:(range_of_lex $loc) exp label_name }
  | "("
    ; exp = seq_expression
    ; ":"
    ; type_ = core_type
    ; ")"
      { Expression.annot ~range:(range_of_lex $loc) exp type_ }
  | "("
    ; exp = seq_expression
    ; ")"
      { exp }

%inline unary_op:
  "-" 
    { Predef_names.neg ~range:(range_of_lex $loc) }

%inline bin_op:
    "+"
      { Predef_names.add ~range:(range_of_lex $loc) }
  | "-"
      { Predef_names.sub ~range:(range_of_lex $loc) }
  | "/"
      { Predef_names.div ~range:(range_of_lex $loc) }
  | "*"
      { Predef_names.mul ~range:(range_of_lex $loc) }
  | ">"
      { Predef_names.greater_than ~range:(range_of_lex $loc) }  
  | "<"
      { Predef_names.less_than ~range:(range_of_lex $loc) }
  | ">="
      { Predef_names.greater_than_equal ~range:(range_of_lex $loc) }
  | "<="
      { Predef_names.less_than_equal ~range:(range_of_lex $loc) }
  | "="
      { Predef_names.equal ~range:(range_of_lex $loc) }
  | "<>"
      { Predef_names.not_equal ~range:(range_of_lex $loc) }
  | "&&"
      { Predef_names.and_ ~range:(range_of_lex $loc) }
  | "||"
      { Predef_names.or_ ~range:(range_of_lex $loc) }

pattern:
    pat = construct_pattern
      { pat }
  | pat = pattern
    ; "as"
    ; var_name = var_name
      { Pattern.alias ~range:(range_of_lex $loc) pat ~as_:var_name }

construct_pattern:
    pat = atom_pattern
      { pat }
  | constr_name = constr_name
    ; arg_pat = pattern
      { Pattern.constr ~range:(range_of_lex $loc) constr_name (Some arg_pat) }
 
atom_pattern:
    const = constant
      { Pattern.const ~range:(range_of_lex $loc) const }
  | "_"     
      { Pattern.any ~range:(range_of_lex $loc) }
  | var_name = var_name            
      { Pattern.var ~range:(range_of_lex $loc) var_name }
  | constr_name = constr_name
      { Pattern.constr ~range:(range_of_lex $loc) constr_name None }
  | "("
    ; pats = separated_nontrivial_list(",", pattern)
    ; ")"
      { Pattern.tuple ~range:(range_of_lex $loc) pats }
  | "{"
    ; label_pats = separated_nonempty_list(";", record_assignment(pattern))
    ; "}"
      { Pattern.record ~range:(range_of_lex $loc) label_pats }
  | "("
    ; pat = pattern
    ; ":"
    ; type_ = core_type
    ; ")"
      { Pattern.annot ~range:(range_of_lex $loc) pat type_ }
  | "("
    ; pat = pattern
    ; ")"
      { pat }  


(** {5 Structures} 

    Structures are simply a list of type definitons, primitive declarations and 
    value bindings. 
*)

core_scheme:
    type_var_names = nonempty_list(type_var_name)
    ; "."
    ; type_ = core_type
      { Type.scheme ~range:(range_of_lex $loc) ~quantifiers:type_var_names type_ }
  | type_ = core_type
      { Type.scheme ~range:(range_of_lex $loc) type_ }

type_declarations:
  "type"
  ; decls = separated_nonempty_list("and", type_declaration)
    { decls }

type_declaration: 
  params = type_param_list 
  ; name = type_name 
  ; kind = type_decl_kind 
      { Structure.type_decl ~range:(range_of_lex $loc) ~name ~params kind }

type_decl_kind:
    (* empty *)
      { Type_decl_abstract }
  | "="
    ; constr_decls = preceded_or_separated_nonempty_list("|", constructor_declaration)
      { Type_decl_variant constr_decls }
  | "="
    ; "{"
    ; label_decls = separated_nonempty_list(";", label_declaration)
    ; "}"
      { Type_decl_record label_decls }

constructor_declaration:
  name = constr_name
  ; arg = option(constructor_argument)
    { Structure.constr_decl ~name ~arg }

label_declaration: 
  name = label_name 
  ; ":"
  ; arg = core_type 
    { Structure.label_decl ~name ~arg }

%inline constructor_argument:
  "of"
  ; type_ = core_type
    { type_ }

%inline type_param_list:
    (* empty *)   
      { [] }
  | type_var_name = type_var_name 
      { [ type_var_name ] }
  | "("
    ; type_var_names = separated_nontrivial_list(",", type_var_name)
    ; ")"
      { type_var_names }

value_description:
    name = var_name 
  ; ":"
  ; scheme = core_scheme 
      { Structure.value_desc ~range:(range_of_lex $loc) ~name ~type_:scheme }

structure_item:
    "let"
    ; value_binding = value_binding
      { Structure.value ~range:(range_of_lex $loc) value_binding }
  | "external"
    ; value_desc = value_description
      { Structure.primitive ~range:(range_of_lex $loc) value_desc }
  | type_decls = type_declarations
      { Structure.type_ ~range:(range_of_lex $loc) type_decls }
  
terminated_structure_item:
  str_item = structure_item
  ; ";;"
    { str_item }

structure:
  structure = nonempty_list(terminated_structure_item)
    { structure }

