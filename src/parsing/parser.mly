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

%type <expression> expression 
%type <sailtype> sailtype
%type <literal> literal
%type <statement> statement
%type <defn> defn

%% 


let sailModule := i = import* ; l = defn* ; EOF ; {fun metadata -> mk_program metadata (ImportSet.of_list i) l}

let brace_del_sep_list(sep,x) == delimited("{", separated_list(sep, x), "}") 

let import := IMPORT ; mname = ID ; {{loc=$loc;mname;dir="";proc_order=1}}

let defn :=
| TYPE ; name = ID ; ty = preceded("=",sailtype)? ; 
    {Type {name; loc = $loc; ty} }

| STRUCT ; name = ID ; g = generic ;  f = brace_del_sep_list(",", id_colon(sailtype)) ;
    {Struct {s_pos=$loc;s_name = name; s_generics = g; s_fields = f}}

| ENUM ; name = ID ; g = generic ; fields = brace_del_sep_list(",", enum_elt) ;
    {Enum {e_pos=$loc;e_name=name; e_generics=g; e_injections=fields}}

| METHOD ; name=ID ; generics=generic ; LPAREN ; params=separated_list(COMMA, mutable_var(sailtype)) ; RPAREN ; rtype=returnType ; body = block ; 
    {Method [{m_proto={pos=$loc;name; generics; params; variadic=false; rtype=rtype }; m_body = Either.right body}]}

| PROCESS ; name = UID ; generics=generic ; interface=parenthesized(interface) ; body =block ;
    {Process ({p_pos=$loc;p_name=name; p_generics=generics; p_interface=interface; p_body=body})}

| EXTERN ; lib=STRING? ; protos =  delimited("{", separated_list(";", extern_sig), "}") ;
    {let protos = List.map (
        fun (sid,p) -> 
            let lib = match lib with Some s -> String.split_on_char ' ' s | None -> [] in 
            {m_proto=p; m_body=Either.left (sid,lib)}
    ) protos in Method protos}


extern_sig : METHOD ; name=ID ; LPAREN ;  params=separated_list(COMMA, mutable_var(sailtype)) ; variadic=is_variadic ; RPAREN ; rtype=returnType ; ext_name=preceded("=",STRING)?
        { (match ext_name with Some n -> n | None -> name),{pos=$loc; name; generics=[]; params; variadic; rtype=rtype} }



is_variadic:
| {false}
| VARARGS {true}

let module_loc :=  
 | ~ = located(ID); DCOLON ; <>
 | x = located(SELF) ; DCOLON; { (fst x),Constants.sail_module_self}

let enum_elt :=
| id = UID ; {(id, [])}
| ~ = UID ; ~ = parenthesized(separated_list(",", sailtype)) ; <>


let generic := {[]} | delimited("<", separated_list(",", UID), ">")


let returnType := preceded(":", sailtype)? 


let interface :=
| {([],[])}
| SIGNAL ; signals = separated_nonempty_list(",",ID); {([], signals)}
| VAR ; global = separated_nonempty_list(",",mutable_var(sailtype)) ; {(global, [])}
| VAR ; ~ = separated_nonempty_list(",", mutable_var(sailtype)) ; ";" ; SIGNAL ; ~ = separated_nonempty_list(",",ID) ; <>


let simpl_expression := 
| located (
    | ~ = ID ; <Variable>
    | ~ = literal ; <Literal>
    | ~ = simpl_expression ; e2 = delimited("[", expression, "]") ; <ArrayRead>
    | ~ = simpl_expression ; "." ; ~ = ID ; <StructRead>
    )
| parenthesized_exp 


let expression :=
| simpl_expression 
| located(
    | "-" ; e = expression ; %prec UNARY {UnOp(Neg, e)} 
    | "!" ; e = expression ; %prec UNARY {UnOp(Not, e)} 
    | "&" ; ~ = mut ; ~ = expression ; %prec UNARY <Ref>
    | "*" ; ~ = expression ; %prec UNARY <Deref>
    | e1 = expression ; op =binOp ; e2 =expression ; { BinOp(op,e1,e2) }
    | ~ = delimited ("[", separated_list(",", expression), "]") ; <ArrayStatic>
    | id=located(ID) ; l = brace_del_sep_list(",", id_colon(expression)) ;
        {
        let m = List.fold_left (fun x (y,(_,z)) -> FieldMap.add y z x) FieldMap.empty l
        in 
        StructAlloc(id, m)
        }
    | id = located(UID) ; {EnumAlloc(id, [])}
    | ~ = located(UID) ; ~ = parenthesized (separated_list(",", expression)) ; <EnumAlloc>
    | m = module_loc ; id = located(ID) ; args = parenthesized(separated_list (",", expression)) ; {MethodCall(Some m, id, args)}
    | id = located(ID) ; args = parenthesized(separated_list (",", expression)) ; {MethodCall(None, id, args)}
)


let id_colon(X) := ~ =ID ; ":" ; ~ = located(X) ; <>

let mutable_var(X) := (loc,id) = located(ID) ; COLON ; mut = boption(MUT) ; ty =X ; { {id;mut;loc;ty} }


let literal :=
| TRUE ; {LBool(true) }
| FALSE ; {LBool(false)}
| ~ = INT ; <LInt>
| ~ = FLOAT ; <LFloat>
| ~ = CHAR ; <LChar>
| ~ = STRING ; <LString>


let parenthesized(e) == delimited("(",e,")")

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
| ~ = delimited("{",statement,"}") ; <Block>
)


let parenthesized_exp == parenthesized(expression)


let iterable_or_range ==
|  rl = INT ; "," ; rr = INT ; {ArrayStatic (List.init (rr - rl) (fun i -> dummy_pos,Literal (LInt (i + rl))))}
| e = expression ; {snd e}

let block_or_statement(b) ==
    | WHILE ; ~ = parenthesized_exp ; ~ = b ; <While>
    | LOOP ; ~ = b ; <Loop>
    | IF ; e = parenthesized_exp ; s1 = b ; {If(e, s1, None)}
    | IF ; e = parenthesized_exp ; s1 = single_statement ; ELSE ; s2 = b ; {If(e, s1, Some s2)}
    | WATCHING ; ~ = ID ; s = b ; <Watching>
    | WHEN ; ~ = ID ; ~ = block ; <When>
    | FOR ; var = ID; IN ; iterable=parenthesized(located(iterable_or_range)) ; body = b ; { For {var;iterable; body} }


let single_statement := 
| located (
    | VAR ; b = mut ; id = ID ; ":" ; typ=sailtype ; {DeclVar(b,id,Some typ,None)}
    | VAR ; b = mut ; id = ID ; ":" ; typ=sailtype ; "=" ; e = expression ; {DeclVar(b,id,Some typ,Some e)}
    | VAR ; b = mut ; id = ID ; "=" ; e = expression ; {DeclVar(b,id,None,Some e)}
    | VAR ; b = mut ; id = ID ; {DeclVar(b,id,None,None)}
    | SIGNAL ; ~ = ID ; <DeclSignal>
    | l = expression ; "=" ; e = expression ; <Assign>
    | CASE ; ~ = parenthesized_exp ; ~ = brace_del_sep_list(",", case) ; <Case>
    | m = module_loc ; l = located(ID) ; args = parenthesized(separated_list(",", expression)) ; {Invoke ((Some m), l, args)}
    | l = located(ID) ; args = parenthesized(separated_list(",", expression)) ; {Invoke (None, l, args)}
    | RETURN ; ~ = expression? ; <Return>
    | ~ = located(UID) ; ~ = parenthesized(separated_list(",", expression )) ; <Run>
    | EMIT ; ~ = ID ; <Emit>
    | AWAIT ; ~ = ID ; <Await>
    | BREAK ; <Break>
    | block_or_statement(single_statement)
    )
| block


let left := block | located (block_or_statement(block))


let statement_seq := 
| single_statement
| terminated(single_statement, ";")
| located (
    | ~ = left ; ~ = statement_seq ; <Seq>
    | ~ = single_statement ; ";" ; ~ = statement_seq ; <Seq>
)


let statement := 
| statement_seq
| located(  ~ = statement_seq ; "||" ; ~ = statement ; <Par>)


let case := separated_pair(pattern, ":", statement)


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
| mloc = module_loc ; name = located(ID) ; generic_instances = instance ; {CompoundType {origin=Some mloc; name; generic_instances} }
| name = located(ID) ; generic_instances = instance ; {CompoundType {origin=None; name; generic_instances}}
| ~ = UID ; <GenericType>
| REF ; b = mut ; t = sailtype ; {RefType(t,b)}


let mut := boption(MUT)


let instance := {[]} | delimited("<", separated_list(",", sailtype), ">")


let located(x) == ~ = x ; { ($loc,x) }
