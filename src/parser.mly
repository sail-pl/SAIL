%{
    open Ast
%}
%token TYPE_BOOL TYPE_INT TYPE_FLOAT TYPE_CHAR TYPE_STRING
%token <int> INT
%token <float> FLOAT
%token <string> ID
%token <string> UID
%token <string> STRING
%token <char> CHAR
%token LPAREN RPAREN LBRACE RBRACE LSQBRACE RSQBRACE LANGLE RANGLE
%token COMMA COLON SEMICOLON
%token DOT
%token QUOTE
%token ASSIGN
%token METHOD PROCESS
%token STRUCT ENUM
%token VAR SIGNAL 
%token IF ELSE WHILE RETURN
%token AWAIT EMIT WATCHING WHEN
%token TRUE FALSE
%token PLUS MINUS MUL DIV REM
%token LE GE EQ NEQ
%token AND OR NOT
%token CASE
%token REF
%token MUT
%token EOF

%left PLUS MINUS
%left MUL DIV REM
%left LE GE EQ  NEQ   
%left AND OR
%nonassoc LANGLE RANGLE
%nonassoc UNARY
%nonassoc RPAREN
%nonassoc ELSE

%start program

%type <Ast.expression> expression 
%type <Ast.sailtype> sailtype
%type <Ast.literal> literal
%type <Ast.lhs> lhs
%type <Ast.declaration> declaration
%type <Ast.statement> statement
%type <Ast.defn> defn
%type <Ast.program> program

%% 

(* for {}; each basic instruction is followed by ; *)

program:  
  | l = list(defn); EOF {mk_program l};
            
defn:
  | STRUCT id = ID g = generic LBRACE f = separated_list(COMMA, id_colon(sailtype)) RBRACE
      {Struct ({s_name = id; s_generics = g; s_fields = f})}
  | ENUM name=ID generics=generic LBRACE fields = separated_list(COMMA, enum_elt) RBRACE
      {Enum {e_name=name; e_generics=generics; e_injections=fields}}
  | METHOD name=ID generics=generic LPAREN params=separated_list(COMMA, id_colon(sailtype)) 
    RPAREN rtype=returnType body=delimited (LBRACE,seq,RBRACE)
      {Method ({m_name=name; m_generics=generics; m_params=params ; m_rtype=rtype; m_body = body})}
  | PROCESS name = UID generics=generic LPAREN interface=interface RPAREN  body=delimited (LBRACE,seq,RBRACE)
      {Process ({p_name=name; p_generics=generics; p_interface=interface; p_body=body})}
  ;

enum_elt :
  | id = UID {(id, [])}
  | id = UID l = delimited(LPAREN, separated_list(COMMA, sailtype), RPAREN) {(id,l)}
; 
generic:
  | {[]}
  | LANGLE params=separated_list(COMMA, UID) RANGLE {params}
  ;

returnType:
|  {None}
|  COLON rtype=sailtype {Some(rtype)};


interface :
  | {([],[])}
  | SIGNAL signals = separated_nonempty_list(COMMA, ID) {([], signals)}
  | VAR global = separated_nonempty_list(COMMA, id_colon(sailtype)) {(global, [])}
  | VAR globals = separated_nonempty_list(COMMA, id_colon(sailtype)) SEMICOLON SIGNAL signals = separated_nonempty_list(COMMA, ID)  {(globals, signals)};

simpl_expression :
| id = ID  {Variable id}
| l = literal {Literal l}
| e1 = simpl_expression e2 = delimited(LSQBRACE, expression, RSQBRACE) {ArrayRead (e1,e2)}
| e = simpl_expression DOT id = ID {StructRead (e,id)}
| e = delimited (LPAREN, expression, RPAREN) {e}

expression :
| e = simpl_expression {e}
| MINUS e = expression %prec UNARY {UnOp(Neg, e)}
| NOT e=expression %prec UNARY {UnOp(Not, e)}
| REF e = expression %prec UNARY {Ref e}
| MUL e= expression %prec UNARY {Deref e}
| e1=expression o=binOp e2=expression {BinOp (o,e1,e2)}
| el = delimited (LSQBRACE, separated_list(SEMICOLON, expression), RSQBRACE) {ArrayStatic(el)}
| l = delimited (LBRACE, separated_list(SEMICOLON, id_colon(expression)), RBRACE) {StructAlloc(l)}
| id = UID {EnumAlloc(id, [])}
| id = UID l = delimited (LPAREN, separated_list(COMMA, expression), RPAREN) {EnumAlloc(id, l)}
| id = ID params = delimited (LPAREN, separated_list (COMMA, expression), RPAREN) {MethodCall (id,params)}

id_colon(X):
  | id=ID COLON x=X {(id,x)}; 

literal :
  | TRUE {LBool(true) }
  | FALSE {LBool(false)}
  | n = INT {LInt n}
  | f = FLOAT {LFloat f}
  | QUOTE c = CHAR QUOTE {LChar c}
  | s = STRING {LString s}
  ;

%inline binOp :
| PLUS {Plus}
| MINUS {Minus}
| MUL {Mul}
| DIV {Div}
| REM {Rem}
| LANGLE {Lt}
| LE {Le}
| RANGLE {Gt}
| GE {Ge}
| EQ {Eq}
| NEQ {NEq}
 |AND {And} 
| OR {Or}
;

declaration :
  | VAR b = mut id = ID COLON typ=sailtype ASSIGN e = expression {VariableDeclaration(b,id,typ,e)}
  | SIGNAL id = ID {SignalDeclaration(id)}
  ;

lhs :
  | id = ID {LHSVar(id)}
  | l = lhs DOT id = ID {LHSField(l, id)}
  | l = lhs e = delimited(LSQBRACE, expression, RSQBRACE) {LHSArray(l,e)}
  ;

seq :
| l = list(statement) 
  {if List.length l <> 1 then Seq l else List.hd l}

parl :
| s1 = statement OR s2 = statement {[s1;s2]}
| s1 = statement OR p = parl {s1::p};

statement :
| d = declaration SEMICOLON {Declaration d}
| l = lhs ASSIGN e = expression SEMICOLON {Assign(l, e)}
| s = delimited(LBRACE,seq, RBRACE) option(SEMICOLON){s}
| s = delimited(LBRACE,parl,RBRACE) {Par s}
| IF e = delimited(LPAREN, expression, RPAREN) s1 = statement  {If(e, s1, None)}
| IF e = delimited(LPAREN, expression, RPAREN) s1 = statement ELSE s2 = statement {If(e, s1, Some s2)}
| WHILE e = delimited(LPAREN, expression, RPAREN) s = statement {While(e, s)}
| CASE e = delimited(LPAREN, expression, RPAREN) l = delimited(LBRACE, list( case), RBRACE) {Case(e,l)}
| id = ID LPAREN p = separated_list(COMMA, expression) RPAREN SEMICOLON {Invoke(None, id, p)}
| RETURN e = option(expression) SEMICOLON {Return e}
| id = UID params=delimited(LPAREN, separated_list(COMMA, expression), RPAREN) SEMICOLON {Run (id, params)}
| EMIT id = delimited(LPAREN, ID, RPAREN) SEMICOLON {Emit(id)}
| AWAIT id = delimited(LPAREN,ID,RPAREN) SEMICOLON {Await(id)}
| WATCHING id = delimited(LPAREN, ID, RPAREN) s = statement {Watching(id, s)}
| WHEN id = delimited(LPAREN, ID, RPAREN) s = statement {When(id, s)}
;

case :
| p = pattern COLON s = statement {(p, s)}
; 

pattern :
| id = ID {PVar id}
| id = UID {PCons (id, [])}
| id = UID l = delimited(LPAREN, separated_list(COMMA, pattern), RPAREN) {PCons(id,l)}
;

sailtype:
  | TYPE_BOOL {Bool}
  | TYPE_INT {Int}
  | TYPE_FLOAT {Float}
  | TYPE_CHAR {Char}
  | TYPE_STRING {String}
  | LSQBRACE typ = sailtype RSQBRACE {ArrayType (typ)}
  | id = ID params=instance {CompoundType(id,params)}
  | name = UID {GenericType(name)}
  | REF b=mut t = sailtype {Ref(t,b)}
  ;

mut:
  | MUT {true}
  | {false}
  ;

instance:
| {[]}
| LANGLE params=separated_list(COMMA, sailtype) RANGLE {params}
