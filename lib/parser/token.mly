// end of file
%token EOF

// keywords
%token LET "let"
%token AND "and"
%token IN "in"
%token IF "if"
%token THEN "then"
%token ELSE "else"
%token FUN "fun"
%token MATCH "match"
%token WITH "with"
%token EXISTS "exists"
%token FORALL "forall"
%token TYPE "type"
%token AS "as"
%token OF "of"
%token EXTERNAL "external"
%token SEMI_SEMI_COLON ";;"

// operators
%token RIGHT_ARROW "->"
%token COLON ":"
%token EQUAL "="
%token DOT "."
%token COMMA ","
%token SEMI_COLON ";"
%token UNDERSCORE "_"
%token QUOTE "'"
%token BAR "|"
%token PLUS "+"
%token MINUS "-"
%token STAR "*"
%token SLASH "/"
%token LESS_GREATER "<>"
%token LESS "<"
%token GREATER ">"
%token LESS_EQUAL "<="
%token GREATER_EQUAL ">="
%token AND_AND "&&"
%token BAR_BAR "||"

// constants
%token CONST_TRUE "true"
%token CONST_FALSE "false"
%token CONST_UNIT "()"
%token <int> CONST_INT "<int>"

// identifiers
%token <string> IDENT "<ident>"
%token <string> UPPER_IDENT "<upper_ident>"

// parens
%token LEFT_PAREN "("
%token RIGHT_PAREN ")"
%token LEFT_BRACE "{" 
%token RIGHT_BRACE "}"

%%