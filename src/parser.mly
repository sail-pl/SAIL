%{

    open Ast

%}

%token <int> INT
%token <string> ID
%token <string> GENERIC_TYPE
%token <string> STRING
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LSQBRACE
%token RSQBRACE
%token COMMA
%token DOT
%token COLON
%token SEMICOLON
%token EXCLAMATION_MARK
%token EQUAL
%token PLUS
%token MINUS
%token MULT
%token DIV
%token REM
%token LANGLE
%token RANGLE
%token AND
%token OR
%token NOT
%token AMPERSAND
%token STAR
%token NEQUAL
%token COLONEQ
%token RARROW
%token VAR
%token SIG
%token TYPE_INT
%token TYPE_FLOAT
%token TYPE_BOOL
%token TYPE_CHAR
%token TYPE_STRING
%token TYPE_VOID
%token STRUCT
%token ENUM
%token PROCESS
%token METHOD
%token TRUE
%token FALSE
%token WHILE
%token IF
%token ELSE
%token RETURN
%token MUT
%token AWAIT
%token EMIT
%token WHEN
%token WATCH
%token SPAWN
%token JOIN
%token EOF

%right COLONEQ EQUAL
%nonassoc AMPERSAND
%left PLUS MINUS LANGLE RANGLE LSQBRACE RSBRACE // check &t[n]
%left MULT DIV REM
%left AND OR

%start program

%type <Ast.program> program
%type <Ast.defn> defn
%type <Ast.expression> expression 
%type <Ast.datatype> datatype
%type <Ast.declaration> declaration
%% 

program:  
| defns=list(defn); EOF {mk_program defns};
            
defn:
| STRUCT name=ID generics=generic LBRACE fields=list(fielddef) RBRACE SEMICOLON 
  {Struct ({s_name=name;s_generics=generics; s_fields=fields})}
| ENUM name=ID generics=generic LBRACE fields=list(fielddef) RBRACE SEMICOLON 
  {Enum {e_name=name; e_generics=generics; e_injections=fields}}
| METHOD name=ID LPAREN params=separated_list(COMMA, param) RPAREN rtype=returnType body=block_expr
  {Method ({m_name=name; m_signature={params=params ;rtype=rtype}; m_body=body;})};

returnType:
|  {None}
|  COLON rtype=datatype {Some(rtype)};

param :
| id=ID COLON t=datatype {(id, t)}

block_expr:
| LBRACE exprs=separated_list(SEMICOLON, statement) RBRACE {exprs}

declaration:
| VAR mut=mut id=ID COLON datatype=datatype EQUAL expr=expression {DeclVar(mut, id, datatype,expr )}
| SIG id=ID {DeclSig(id)};

expression :
| id=ID {Var id}
| constant=litteral {Lit(constant)};

(* sig -> type *)
litteral :
  | v = INT {LInt v};


statement :
| decl=declaration {Decl(decl)}
| target=expression EQUAL value=expression {Assign(target, value)}
| IF cond_expr=expression then_expr=block_expr else_expr=option(else_branch) {If(cond_expr, then_expr, else_expr)}
| WHILE cond_expr=expression loop_expr=block_expr {While(cond_expr, loop_expr)}
| RETURN retval=option(expression) {Return retval} 

else_branch:
  | ELSE; expr=block_expr {expr};

generic:
| {[]}
| LANGLE params=separated_list(COMMA, GENERIC_TYPE) RANGLE {params};

instance:
| {[]}
| LANGLE params=separated_list(COMMA, datatype) RANGLE {params}
      
fielddef:
  | id=ID COLON datatype=datatype SEMICOLON{(id, datatype)};

mut:
  | {false}
  | MUT {true};

datatype:
  | TYPE_INT {Int}
  | TYPE_FLOAT {Float}
  | TYPE_BOOL {Bool}
  | TYPE_CHAR {Char}
  | TYPE_STRING {String}
  | TYPE_VOID {Void}
  | datatype=datatype LSQBRACE size=INT RSQBRACE {Array (datatype, size)} // shift-reduce 
  | AMPERSAND mut=mut datatype=datatype {Ref(mut, datatype)}
  | id = ID params=instance {Compound (id, params)}
  | name = GENERIC_TYPE {Generic(name)};

/* ; method_defns=list(method_defn); process_defns=list(process_defn)*/
