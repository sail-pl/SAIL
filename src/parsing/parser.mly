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
    open Common
    open TypesCommon
    open AstParser
%}
%token TYPE_BOOL TYPE_INT TYPE_FLOAT TYPE_CHAR TYPE_STRING
%token TYPE
%token <int> INT
%token <float> FLOAT
%token <string> ID
%token <string> UID
%token <string> STRING
%token <char> CHAR

%token LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}" LSQBRACE "[" RSQBRACE "]" LANGLE "<" RANGLE ">" (* ARROW "->" *)
%token COMMA "," COLON ":" DCOLON "::" SEMICOLON ";" DOT "."
%token ASSIGN "="
%token IMPORT
%token EXTERN
%token VARARGS
%token METHOD PROCESS STRUCT ENUM 
%token VAR SIGNAL 
%token IF ELSE WHILE RETURN BREAK
%token AWAIT EMIT WATCHING WHEN PAR "||"
%token TRUE FALSE 
%token PLUS "+" MINUS "-" MUL "*" DIV "/" REM "%"
%token LE "<=" GE ">=" EQ "==" NEQ "!="
%token AND OR NOT "!"
%token CASE
%token REF "&"
%token MUT
%token ARRAY
%token SELF
%token LOOP
%token FOR
%token IN
%token EOF

%left AND OR
%left "<" ">" "<=" ">=" "==" "!="
%left "+" "-"
%left "*" "/" "%"

%nonassoc UNARY
%nonassoc ")"
%nonassoc ELSE

%start <metadata -> statement SailModule.t E.t> sailModule

%% 

let sailModule := i = import* ; l = defn* ; EOF ; {fun metadata -> mk_program metadata (ImportSet.of_list i) l}

let defn ==
| TYPE ; name = ID ; ty = preceded("=",sailtype)? ; 
    {Type {name; loc = $loc; ty} }

| STRUCT ; s_name = ID ; s_generics = generic ; s_fields = brace_del_sep_list(",", id_colon(sailtype)) ;
    {Struct {s_pos=$loc;s_name; s_generics; s_fields}}

| ENUM ; e_name = ID ; e_generics = generic ; e_injections = brace_del_sep_list(",", enum_elt) ;
    {Enum {e_pos=$loc;e_name; e_generics; e_injections}}

| METHOD ; name=ID ; generics=generic ; LPAREN ; params=separated_list(COMMA, mutable_var(sailtype)) ; RPAREN ; rtype=returnType ; body = block ; 
    {Method [{m_proto={pos=$loc;name; generics; params; variadic=false; rtype=rtype }; m_body = Either.right body}]}

| PROCESS ; p_name = UID ; p_generics=generic ; p_interface=parenthesized(interface) ; p_body =block ;
    {Process ({p_pos=$loc;p_name; p_generics; p_interface; p_body})}

| EXTERN ; lib=STRING? ; protos =  delimited("{", separated_nonempty_list_opt(";", extern_sig), "}") ;
    {let protos = List.map (
        fun (sid,p) -> 
            let lib = match lib with Some s -> String.split_on_char ' ' s | None -> [] in 
            {m_proto=p; m_body=Either.left (sid,lib)}
    ) protos in Method protos}


let extern_sig == METHOD ; name=ID ; LPAREN ;  params=separated_list(COMMA, mutable_var(sailtype)) ; variadic=boption(VARARGS) ; RPAREN ; rtype=returnType ; ext_name=preceded("=",STRING)? ;
        { (match ext_name with Some n -> n | None -> name),{pos=$loc; name; generics=[]; params; variadic; rtype=rtype} }

let enum_elt ==  ~ = UID ; ~ = loption(parenthesized(separated_list(",", sailtype))) ; <>

let import == IMPORT ; mname = ID ; {{loc=$loc;mname;dir="";proc_order=1}}

let generic == loption(delimited("<", separated_list(",", UID), ">"))

let returnType == preceded(":", sailtype)? 

let mutable_var(X) == (loc,id) = located(ID) ; COLON ; mut = mut ; ty =X ; { {id;mut;loc;ty} }

let separated_nonempty_list_opt(separator, X) :=
  x = X ; separator?  ; { [ x ] }
| x = X; separator; xs = separated_nonempty_list_opt(separator, X) ; { x :: xs }


let interface ==
| {([],[])}
| SIGNAL ; signals = separated_nonempty_list(",",ID); {([], signals)}
| VAR ; global = separated_nonempty_list(",",mutable_var(sailtype)) ; {(global, [])}
| VAR ; ~ = separated_nonempty_list(",", mutable_var(sailtype)) ; ";" ; SIGNAL ; ~ = separated_nonempty_list(",",ID) ; <>

let block == located (
| "{" ; "}" ; {Skip}
| ~ = delimited("{",statement,"}") ; <Block>
)


let simpl_expression := 
| located (
    | ~ = ID ; <Variable>
    | ~ = literal ; <Literal>
    | ~ = simpl_expression ; e2 = delimited("[", expression, "]") ; <ArrayRead>
    | ~ = simpl_expression ; "." ; ~ = located(ID) ; <StructRead>
    )
| parenthesized(expression) 


let expression :=
| simpl_expression 
| located(
    | "-" ; e = expression ; %prec UNARY {UnOp(Neg, e)} 
    | "!" ; e = expression ; %prec UNARY {UnOp(Not, e)} 
    | "&" ; ~ = mut ; ~ = expression ; %prec UNARY <Ref>
    | "*" ; ~ = expression ; %prec UNARY <Deref>
    | e1 = expression ; op =binOp ; e2 =expression ; { BinOp(op,e1,e2) }
    | ~ = delimited ("[", separated_list(",", expression), "]") ; <ArrayStatic>
    | mloc  = ioption(module_loc) ; id=located(ID) ; l = brace_del_sep_list(",", id_colon(expression)) ;
        { let m = List.fold_left (fun l (y,(_,z)) -> (y,z)::l) [] l in StructAlloc(mloc,id, m) }
    | ~ = located(UID) ; ~ = loption(parenthesized (separated_list(",", expression))) ; <EnumAlloc>
    | ~ = ioption(module_loc) ; ~ = located(ID) ; ~ = parenthesized(separated_list (",", expression)) ; <MethodCall>
)

let id_colon(X) == ~ =ID ; ":" ; ~ = located(X) ; <>

let literal ==
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


let block_or_statement(b) ==
    | WHILE ; ~ = parenthesized(expression) ; ~ = b ; <While>
    | LOOP ; ~ = b ; <Loop>
    | IF ; e = parenthesized(expression) ; s1 = b ; {If(e, s1, None)}
    | IF ; e = parenthesized(expression) ; s1 = single_statement ; ELSE ; s2 = b ; {If(e, s1, Some s2)}
    | WATCHING ; ~ = ID ; s = b ; <Watching>
    | WHEN ; ~ = ID ; ~ = block ; <When>
    | FOR ; var = ID; IN ; iterable=parenthesized(located(iterable_or_range)) ; body = b ; { For {var;iterable; body} }


let iterable_or_range ==
|  rl = INT ; "," ; rr = INT ; {ArrayStatic (List.init (rr - rl) (fun i -> dummy_pos,Literal (LInt (i + rl))))}
| e = expression ; {snd e}


let single_statement := 
| located (
    | VAR ; ~ = mut ; ~ = ID ; ~ = preceded(":", sailtype)? ; ~ = preceded("=",expression)? ; <DeclVar>
    | SIGNAL ; ~ = ID ; <DeclSignal>
    | l = expression ; "=" ; e = expression ; <Assign>
    | CASE ; ~ = parenthesized(expression) ; ~ = brace_del_sep_list(",", case) ; <Case>
    | ~ = ioption(module_loc) ; ~ = located(ID) ; ~ = parenthesized(separated_list(",", expression)) ; <Invoke>
    | RETURN ; ~ = expression? ; <Return>
    | ~ = located(UID) ; ~ = parenthesized(separated_list(",", expression )) ; <Run>
    | EMIT ; ~ = ID ; <Emit>
    | AWAIT ; ~ = ID ; <Await>
    | BREAK ; <Break>
    | block_or_statement(single_statement)
    )
| block


let brace_del_sep_list(sep,x) == delimited("{", separated_nonempty_list_opt(sep, x), "}") 

let located(x) == ~ = x ; { ($loc,x) }

let case == separated_pair(pattern, ":", statement)

let mut == boption(MUT)

let module_loc ==  ~ = located(ID); DCOLON ; <> | x = located(SELF) ; DCOLON; { (fst x),Constants.sail_module_self}

let parenthesized(e) == delimited("(",e,")")


let statement_seq := 
| single_statement
| terminated(single_statement, ";")
| located (
    | ~ = left ; ~ = statement_seq ; <Seq>
    | ~ = single_statement ; ";" ; ~ = statement_seq ; <Seq>
)

let left == block | located (block_or_statement(block))

let statement := 
| statement_seq
| located(  ~ = statement_seq ; "||" ; ~ = statement ; <Par>)


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
| mloc = ioption(module_loc) ; name = located(ID) ; generic_instances = instance ; {CompoundType {origin=mloc; name; generic_instances; decl_ty=None} }
| ~ = UID ; <GenericType>
| REF ; b = mut ; t = sailtype ; {RefType(t,b)}


let instance == loption(delimited("<", separated_list(",", sailtype), ">"))