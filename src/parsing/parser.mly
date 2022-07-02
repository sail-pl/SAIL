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
%token AND OR NOT 
%token CASE
%token REF
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
    {Struct ({s_pos=$loc;s_name = name; s_generics = g; s_fields = f})}
| ENUM ; name = ID ; g = generic ; "{" ; fields = separated_list(",", enum_elt) ; "}" ;
    {Enum {e_pos=$loc;e_name=name; e_generics=g; e_injections=fields}}
| proto = fun_sig ; body = block ; {Method {m_proto=proto; m_body = body}}
| PROCESS ; name = UID ; generics=generic ; "(" ; interface=interface ; ")" ; body=block ;
    {Process ({p_pos=$loc;p_name=name; p_generics=generics; p_interface=interface; p_body=body})}
| EXTERN ; "{" ; protos = separated_list(";",fun_sig) ; "}" ; {Ffi protos}


let fun_sig :=  METHOD ; name=ID ; generics=generic ; "(" ; params=separated_list(",", id_colon(sailtype)) ; ")" ; rtype=returnType ; 
    {({pos=$loc;name=name; generics=generics; params=params ; rtype=rtype})}


let enum_elt :=
| id = UID ; {(id, [])}
| id = UID ; l = delimited("(", separated_list(",", sailtype), ")") ; {(id,l)}


let generic := {[]} | "<" ; params=separated_list(",", UID) ; ">" ; {params}


let returnType := {None} | ":" ; rtype=sailtype ; {Some(rtype)}


let interface :=
| {([],[])}
| SIGNAL ; signals = separated_nonempty_list(",", ID) ; {([], signals)}
| VAR ; global = separated_nonempty_list(",", id_colon(sailtype)) ; {(global, [])}
| VAR ; globals = separated_nonempty_list(",", id_colon(sailtype)) ; ";" ; SIGNAL ; signals = separated_nonempty_list(",", ID) ; {(globals, signals)}


let simpl_expression :=
| id = ID ; {Variable ($loc,id)}
| l = literal ; {Literal ($loc,l)}
| e1 = simpl_expression ; e2 = delimited("[", expression, "]") ; {ArrayRead ($loc,e1,e2)}
| e = simpl_expression ; "." ; id = ID ; {StructRead ($loc,e,id)}
| e = delimited ("(", expression, ")") ; {e}


let expression :=
| e = simpl_expression ; {e}
| MINUS ; e = expression ; %prec UNARY {UnOp($loc,Neg, e)} 
| NOT ; e=expression ; %prec UNARY {UnOp($loc,Not, e)} 
| REF ; MUT ; e = expression ; %prec UNARY {Ref ($loc,true,e)} 
| REF ; e = expression ; %prec UNARY {Ref ($loc,false,e)} 
| MUL ; e = expression ; %prec UNARY {Deref ($loc,e)} 
| e1=expression ; o=binOp ; e2=expression ; {BinOp ($loc,o,e1,e2)}
| el = delimited ("[", separated_list(",", expression), "]") ; {ArrayStatic($loc,el)}
| id=ID ; l = delimited ("{", separated_nonempty_list(",", id_colon(expression)), "}") ;
    {
      let m = List.fold_left (fun x (y,z) -> FieldMap.add y z x) FieldMap.empty l
      in StructAlloc($loc,id, m)
    }
| id = UID ; {EnumAlloc($loc,id, [])}
| id = UID ; l = delimited ("(", separated_list(",", expression), ")") ; {EnumAlloc($loc,id, l)}
| id = ID ; params = delimited ("(", separated_list (",", expression), ")") ; {MethodCall ($loc,id,params)}


let id_colon(X) := id=ID ; ":" ; x=X ; {(id,x)}


let literal :=
| TRUE ; {LBool(true) }
| FALSE ; {LBool(false)}
| n = INT ; {LInt n}
| f = FLOAT ; {LFloat f}
| c = CHAR ; {LChar c}
| s = STRING ; {LString s}


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


let block := 
| "{" ; "}" ; {Skip $loc} 
| "{" ; s = statement ; "}" ; {Block ($loc, s)}


let single_statement :=
| VAR ; b = mut ; id = ID ; ":" ; typ=sailtype ; {DeclVar($loc,b,id,Some typ,None)}
| VAR ; b = mut ; id = ID ; ":" ; typ=sailtype ; "=" ; e = expression ; {DeclVar($loc,b,id,Some typ,Some e)}
| VAR ; b = mut ; id = ID ; "=" ; e = expression ; {DeclVar($loc,b,id,None,Some e)}
| VAR ; b = mut ; id = ID ; {DeclVar($loc,b,id,None,None)}
| SIGNAL ; id = ID ; {DeclSignal($loc,id)}
| l = expression ; "=" ; e = expression ; {Assign($loc,l, e)}
| IF ; e = delimited("(", expression, ")") ; s1 = single_statement ; {If($loc,e, s1, None)}
| IF ; e = delimited("(", expression, ")") ; s1 = single_statement ; ELSE ; s2 = single_statement ; {If($loc,e, s1, Some s2)}
| WHILE ; e = delimited("(", expression, ")") ; s = single_statement ; {While($loc,e, s)}
| CASE ; e = delimited("(", expression, ")") ; l = delimited("{", separated_list(",",case), "}") ; {Case($loc,e,l)}
| id = ID ; "(" ; p = separated_list(",", expression) ; ")" ; {Invoke($loc,None, id, p)}
| RETURN ; e = expression? ; {Return ($loc, e)}
| id = UID ; params=delimited("(", separated_list(",", expression), ")") ; {Run ($loc,id, params)}
| EMIT ; id = ID ; {Emit($loc,id)}
| AWAIT ; id = ID ; {Await($loc,id)}
| WATCHING ; id = ID ; s = single_statement ; {Watching($loc,id, s)}
| WHEN ; id = ID ; s = single_statement ;  {When($loc,id, s)}
| s = block ; {s}


let left :=
| s1 = block ; {s1}
| IF ; e = delimited("(", expression, ")") ; s1 = block ; {If($loc,e, s1, None)}
| IF ; e = delimited("(", expression, ")") ; s1 = single_statement ; ELSE ; s2 = block ; {If($loc,e, s1, Some s2)}
| WHILE ; e = delimited("(", expression, ")") ; s = block ; {While($loc,e, s)}
| WATCHING ; id = ID ; s = block ; {Watching($loc,id, s)}
| WHEN ; id = ID ; s = block ; {When($loc,id, s)}


let statement_seq := 
| s = single_statement ; {s}
| s = single_statement ; ";" ; {s}
| s1 = left ; s2 = statement_seq ; {Seq($loc,s1, s2)}
| s1 = single_statement ; ";" ; s2 = statement_seq ; {Seq($loc,s1,s2)}


let statement :=
| s = statement_seq ; {s}
| s1 = statement_seq ; "||" ; s2 = statement ; {Par ($loc,s1, s2)}


let case := p = pattern ; ":" ; s = statement ; {(p, s)}


let pattern :=
| id = ID ; {PVar id}
| id = UID ; {PCons (id, [])}
| id = UID ; l = delimited("(", separated_list(",", pattern), ")") ; {PCons(id,l)}


let sailtype :=
| TYPE_BOOL ; {Bool}
| TYPE_INT ; {Int}
| TYPE_FLOAT ; {Float}
| TYPE_CHAR ; {Char}
| TYPE_STRING ; {String}
| ARRAY ; "<" ; typ = sailtype ; ";" ; size=INT ; ">" ; {ArrayType (typ, size)}
| id = ID ; params=instance ; {CompoundType(id,params)}
| name = UID ; {GenericType(name)}
| REF ; b=mut ; t = sailtype ; {RefType(t,b)}


let mut := MUT ; {true} | {false}


let instance := {[]} | "<" ; params=separated_list(",", sailtype) ; ">" ; {params}
