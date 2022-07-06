(**************************************************************************)
(*                                                                        *)
(*                                 SAIL                                   *)
(*                                                                        *)
(*             Frédéric Dabrowski, LMV, Orléans University                *)
(*                                                                        *)
(* Copyright (C) 2022 Frédéric Dabrowski                                  *)
(*                                                                        *)
(* This program is free software: you can redistribute it and/or modify   *)
(* it under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or      *)
(* (at your option) any later version.                                    *)
(*                                                                        *)
(* This program is distributed in the hope that it will be useful,        *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of         *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          *)
(* GNU General Public License for more details.                           *)
(*                                                                        *)
(* You should have received a copy of the GNU General Public License      *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>. *)
(**************************************************************************)

%{
    open Common.TypesCommon
    open AstParser
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
%token ASSIGN
%token EXTERN
%token METHOD PROCESS
%token STRUCT ENUM
%token VAR SIGNAL 
%token IF ELSE WHILE RETURN
%token AWAIT EMIT WATCHING WHEN
%token TRUE FALSE
%token PLUS MINUS MUL DIV REM
%token LE GE EQ NEQ
%token AND OR NOT PAR
%token CASE
%token REF
%token MUT
%token ARRAY
%token EOF

%left AND OR
%left RANGLE LANGLE LE GE EQ NEQ
%left PLUS MINUS
%left MUL DIV REM

%nonassoc UNARY

%nonassoc RPAREN

%nonassoc ELSE

%start sailModule

%type <expression> expression 
%type <sailtype> sailtype
%type <literal> literal
%type <statement> statement
%type <defn> defn
%type <string -> statement sailModule> sailModule

%% 

sailModule:  
| l = list(defn); EOF {fun x -> mk_program x l};
            
defn:
| STRUCT id = ID g = generic LBRACE f = separated_list(COMMA, id_colon(sailtype)) RBRACE
    {Struct ({s_pos=$loc;s_name = id; s_generics = g; s_fields = f})}
| ENUM name=ID generics=generic LBRACE fields = separated_list(COMMA, enum_elt) RBRACE
    {Enum {e_pos=$loc;e_name=name; e_generics=generics; e_injections=fields}}
| proto = fun_sig body = block {Method {m_proto=proto; m_body = body}}

| PROCESS name = UID generics=generic LPAREN interface=interface RPAREN  body=block
    {Process ({p_pos=$loc;p_name=name; p_generics=generics; p_interface=interface; p_body=body})}

| EXTERN LBRACE protos = separated_list(SEMICOLON,fun_sig) RBRACE {Ffi protos}
;



fun_sig : METHOD name=ID generics=generic LPAREN params=separated_list(COMMA, id_colon(sailtype)) RPAREN rtype=returnType 
        {({pos=$loc;name=name; generics=generics; params=params ; rtype=rtype})}
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
| id = ID  {Variable ($loc,id)}
| l = literal {Literal ($loc,l)}
| e1 = simpl_expression e2 = delimited(LSQBRACE, expression, RSQBRACE) {ArrayRead ($loc,e1,e2)}
| e = simpl_expression DOT id = ID {StructRead ($loc,e,id)}
| e = delimited (LPAREN, expression, RPAREN) {e}

expression :
| e = simpl_expression {e}
| MINUS e = expression %prec UNARY {UnOp($loc,Neg, e)}
| NOT e=expression %prec UNARY {UnOp($loc,Not, e)}
| REF MUT e = expression %prec UNARY {Ref ($loc,true,e)}
| REF e = expression %prec UNARY {Ref ($loc,false,e)}
| MUL e = expression %prec UNARY {Deref ($loc,e)}
| e1=expression o=binOp e2=expression {BinOp ($loc,o,e1,e2)}
| el = delimited (LSQBRACE, separated_list(COMMA, expression), RSQBRACE) {ArrayStatic($loc,el)}
| id=ID l = delimited (LBRACE, separated_nonempty_list(COMMA, id_colon(expression)), RBRACE) 
    {
      let m = List.fold_left (fun x (y,z) -> FieldMap.add y z x) FieldMap.empty l
      in StructAlloc($loc,id, m)
      }
| id = UID {EnumAlloc($loc,id, [])}
| id = UID l = delimited (LPAREN, separated_list(COMMA, expression), RPAREN) {EnumAlloc($loc,id, l)}
| id = ID params = delimited (LPAREN, separated_list (COMMA, expression), RPAREN) {MethodCall ($loc,id,params)}

id_colon(X):
| id=ID COLON x=X {(id,x)}; 

literal :
| TRUE {LBool(true) }
| FALSE {LBool(false)}
| n = INT {LInt n}
| f = FLOAT {LFloat f}
| c = CHAR {LChar c}
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
| AND {And} 
| OR {Or}
;

block :
| LBRACE RBRACE {Skip $loc}
| LBRACE s = statement RBRACE {Block ($loc, s)}
;

single_statement :
| VAR b = mut id = ID COLON typ=sailtype  {DeclVar($loc,b,id,Some typ,None)}
| VAR b = mut id = ID COLON typ=sailtype ASSIGN e = expression  {DeclVar($loc,b,id,Some typ,Some e)}
| VAR b = mut id = ID ASSIGN e = expression  {DeclVar($loc,b,id,None,Some e)}
| VAR b = mut id = ID  {DeclVar($loc,b,id,None,None)}
| SIGNAL id = ID  {DeclSignal($loc,id)}
| l = expression ASSIGN e = expression {Assign($loc,l, e)}
| IF e = delimited(LPAREN, expression, RPAREN) s1 = single_statement  {If($loc,e, s1, None)}
| IF e = delimited(LPAREN, expression, RPAREN) s1 = single_statement ELSE s2 = single_statement {If($loc,e, s1, Some s2)}
| WHILE e = delimited(LPAREN, expression, RPAREN) s = single_statement {While($loc,e, s)}
| CASE e = delimited(LPAREN, expression, RPAREN) l = delimited(LBRACE, separated_list(COMMA,case), RBRACE) {Case($loc,e,l)}
| id = ID LPAREN p = separated_list(COMMA, expression) RPAREN  {Invoke($loc,None, id, p)}
| RETURN e = option(expression)  {Return ($loc, e)}
| id = UID params=delimited(LPAREN, separated_list(COMMA, expression), RPAREN)  {Run ($loc,id, params)}
| EMIT id = ID  {Emit($loc,id)}
| AWAIT id = ID  {Await($loc,id)}
| WATCHING id = ID s = single_statement {Watching($loc,id, s)}
| WHEN id = ID s = single_statement {When($loc,id, s)}
| s = block {s}

left : 
| s1 = block {s1}
| IF e = delimited(LPAREN, expression, RPAREN) s1 = block  {If($loc,e, s1, None)}
| IF e = delimited(LPAREN, expression, RPAREN) s1 = single_statement ELSE s2 = block {If($loc,e, s1, Some s2)}
| WHILE e = delimited(LPAREN, expression, RPAREN) s = block{While($loc,e, s)}
| WATCHING id = ID s = block {Watching($loc,id, s)}
| WHEN id = ID s = block {When($loc,id, s)}
;

statement_seq : 
| s = single_statement {s}
| s = single_statement SEMICOLON {s}
| s1 = left s2 = statement_seq {Seq($loc,s1, s2)}
| s1 = single_statement SEMICOLON s2 = statement_seq {Seq($loc,s1,s2)}
;

statement :
| s = statement_seq {s}
| s1 = statement_seq PAR  s2 = statement {Par ($loc,s1, s2)}
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
| ARRAY LANGLE typ = sailtype SEMICOLON size=INT RANGLE {ArrayType (typ, size)}
| id = ID params=instance {CompoundType(id,params)}
| name = UID {GenericType(name)}
| REF b=mut t = sailtype {RefType(t,b)}
;

mut:
| MUT {true}
| {false}
;

instance:
| {[]}
| LANGLE params=separated_list(COMMA, sailtype) RANGLE {params}
;