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

%token LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}" LSQBRACE "[" RSQBRACE "]" LANGLE "<" RANGLE ">"
%token COMMA "," COLON ":" SEMICOLON ";" DOT "."
%token ASSIGN "="
%token EXTERN
%token METHOD PROCESS STRUCT ENUM 
%token VAR SIGNAL 
%token IF ELSE WHILE RETURN
%token AWAIT EMIT WATCHING WHEN PAR "||"
%token TRUE FALSE 
%token PLUS "+" MINUS "-" MUL "*" DIV "/" REM "%"
%token LE "<=" GE ">=" EQ "==" NEQ "!="
%token AND OR NOT "!"
%token CASE
%token REF "&"
%token MUT
%token ARRAY
%token EOF

%left AND OR
%left "<" ">" "<=" ">=" "==" "!="
%left "+" "-"
%left "*" "/" "%"

%nonassoc UNARY

%nonassoc ")"

%nonassoc ELSE

%start <string -> statement sailModule> sailModule

%type <expression> expression 
%type <sailtype> sailtype
%type <literal> literal
%type <statement> statement
%type <defn> defn

%% 


let sailModule := l = defn* ; EOF ; {fun x -> mk_program x l}


let defn :=
| STRUCT ; name = ID ; g = generic ; "{" ; f = separated_list(",", id_colon(sailtype)) ; "}" ;
    {Struct {s_pos=$loc;s_name = name; s_generics = g; s_fields = f}}
| ENUM ; name = ID ; g = generic ; "{" ; fields = separated_list(",", enum_elt) ; "}" ;
    {Enum {e_pos=$loc;e_name=name; e_generics=g; e_injections=fields}}
| proto = fun_sig ; body = block ; {Method {m_proto=proto; m_body = body}}
| PROCESS ; name = UID ; generics=generic ; "(" ; interface=interface ; ")" ; body=block ;
    {Process ({p_pos=$loc;p_name=name; p_generics=generics; p_interface=interface; p_body=body})}
| EXTERN ; "{" ; ~ = separated_list(";",fun_sig) ; "}" ; <Ffi>


let fun_sig :=  METHOD ; name=ID ; generics=generic ; "(" ; params=separated_list(",", id_colon(sailtype)) ; ")" ; rtype=returnType ; 
    {({pos=$loc;name=name; generics=generics; params=params ; rtype=rtype})}


let enum_elt :=
| id = UID ; {(id, [])}
| ~ = UID ; ~ = delimited("(", separated_list(",", sailtype), ")") ; <>


let generic := {[]} | "<" ; ~ =separated_list(",", UID) ; ">" ; <>


let returnType := {None} | ":" ; ~ = sailtype ; <Some>


let interface :=
| {([],[])}
| SIGNAL ; signals = separated_nonempty_list(",", ID) ; {([], signals)}
| VAR ; global = separated_nonempty_list(",", id_colon(sailtype)) ; {(global, [])}
| VAR ; ~ = separated_nonempty_list(",", id_colon(sailtype)) ; ";" ; SIGNAL ; ~ = separated_nonempty_list(",", ID) ; <>


let simpl_expression := 
| located (
    | ~ = ID ; <Variable>
    | ~ = literal ; <Literal>
    | ~ = simpl_expression ; e2 = delimited("[", expression, "]") ; <ArrayRead>
    | ~ = simpl_expression ; "." ; ~ = ID ; <StructRead>
    )
| ~ = delimited ("(", expression, ")") ; <>


let expression :=
| ~ = simpl_expression ; <>
| located(
    | "-" ; e = expression ; %prec UNARY {UnOp(Neg, e)} 
    | "!" ; e=expression ; %prec UNARY {UnOp(Not, e)} 
    | "&" ; MUT ; e = expression ; %prec UNARY {Ref (true,e)} 
    | "&" ; e = expression ; %prec UNARY {Ref (false,e)} 
    | "*" ; ~ = expression ; %prec UNARY <Deref>
    | e1 = expression ; op =binOp ; e2 =expression ; { BinOp(op,e1,e2) }
    | ~ = delimited ("[", separated_list(",", expression), "]") ; <ArrayStatic>
    | id=ID ; l = delimited ("{", separated_nonempty_list(",", id_colon(expression)), "}") ;
        {
        let m = List.fold_left (fun x (y,z) -> FieldMap.add y z x) FieldMap.empty l
        in 
        StructAlloc(id, m)
        }
    | id = UID ; {EnumAlloc(id, [])}
    | ~ = UID ; ~ = delimited ("(", separated_list(",", expression), ")") ; <EnumAlloc>
    | ~ = ID ; ~ = delimited ("(", separated_list (",", expression), ")") ; <MethodCall>
)


let id_colon(X) := ~ =ID ; ":" ; ~ =X ; <>


let literal :=
| TRUE ; {LBool(true) }
| FALSE ; {LBool(false)}
| ~ = INT ; <LInt>
| ~ = FLOAT ; <LFloat>
| ~ = CHAR ; <LChar>
| ~ = STRING ; <LString>


let binOp ==
| "+" ; {Plus} 
| "-" ; {Minus}
| "*" ; {Mul}
| "/" ; {Div}
| "%" ; {Rem}
| "<" ; {Lt}
| "<=" ; {Le}
| ">" ; {Gt}
| ">=" ; {Ge}
| "==" ; {Eq}
| "!=" ; {NEq}
| AND ; {And} 
| OR ; {Or}


let block := located (
| "{" ; "}" ; {Skip}
| "{" ; ~ = statement ; "}" ; <Block>
)



let single_statement := 
| located (
    | VAR ; b = mut ; id = ID ; ":" ; typ=sailtype ; {DeclVar(b,id,Some typ,None)}
    | VAR ; b = mut ; id = ID ; ":" ; typ=sailtype ; "=" ; e = expression ; {DeclVar(b,id,Some typ,Some e)}
    | VAR ; b = mut ; id = ID ; "=" ; e = expression ; {DeclVar(b,id,None,Some e)}
    | VAR ; b = mut ; id = ID ; {DeclVar(b,id,None,None)}
    | SIGNAL ; ~ = ID ; <DeclSignal>
    | l = expression ; "=" ; e = expression ; {Assign(l, e)}
    | IF ; e = delimited("(", expression, ")") ; s1 = single_statement ; {If(e, s1, None)}
    | IF ; e = delimited("(", expression, ")") ; s1 = single_statement ; ELSE ; s2 = single_statement ; {If(e, s1, Some s2)}
    | WHILE ; ~ = delimited("(", expression, ")") ; ~ = single_statement ; <While>
    | CASE ; ~ = delimited("(", expression, ")") ; ~ = delimited("{", separated_list(",",case), "}") ; <Case>
    | ~ = ID ; "(" ; ~ = separated_list(",", expression) ; ")" ; <Invoke>
    | RETURN ; ~ = expression? ; <Return>
    | ~ = UID ; ~ =delimited("(", separated_list(",", expression ), ")") ; <Run>
    | EMIT ; ~ = ID ; <Emit>
    | AWAIT ; ~ = ID ; <Await>
    | WATCHING ; ~ = ID ; ~ = single_statement ; <Watching>
    | WHEN ; ~ = ID ; ~ = single_statement ;  <When>
    )
| ~ = block ; <>


let left :=
| ~ = block ; <>
| located (
    | IF ; e = delimited("(", expression, ")") ; s1 = block ; {If(e, s1, None)}
    | IF ; e = delimited("(", expression, ")") ; s1 = single_statement ; ELSE ; s2 = block ; {If(e, s1, Some s2)}
    | WHILE ; ~ = delimited("(", expression, ")") ; ~ = block ; <While>
    | WATCHING ; ~ = ID ; s = block ; <Watching>
    | WHEN ; ~ = ID ; ~ = block ; <When>
)


let statement_seq := 
| ~ = single_statement ; <>
| ~ = single_statement ; ";" ; <>
| located (
    | ~ = left ; ~ = statement_seq ; <Seq>
    | ~ = single_statement ; ";" ; ~ = statement_seq ; <Seq>
)


let statement := 
|  ~ = statement_seq ; <>
| located(  ~ = statement_seq ; "||" ; ~ = statement ; <Par>)


let case := ~ = pattern ; ":" ; ~ = statement ; <>


let pattern :=
| ~ = ID ; <PVar>
| id = UID ; {PCons (id, [])}
| ~ = UID ; ~ = delimited("(", separated_list(",", pattern), ")") ; <PCons>


let sailtype :=
| TYPE_BOOL ; {Bool}
| TYPE_INT ; {Int}
| TYPE_FLOAT ; {Float}
| TYPE_CHAR ; {Char}
| TYPE_STRING ; {String}
| ARRAY ; "<" ; ~ = sailtype ; ";" ; ~ = INT ; ">" ; <ArrayType>
| ~ = ID ; ~ = instance ; <CompoundType>
| ~ = UID ; <GenericType>
| REF ; b = mut ; t = sailtype ; {RefType(t,b)}


let mut := MUT ; {true} | {false}


let instance := {[]} | "<" ; ~ =separated_list(",", sailtype) ; ">" ; <>


let located(x) == ~ = x ; { ($loc,x) }
