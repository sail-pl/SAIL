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
%token TYPE_BOOL TYPE_FLOAT TYPE_CHAR TYPE_STRING
%token <int> TYPE_INT 
%token TYPE
%token <Z.t> INT
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
%token VAR 
//SIGNAL 
%token IF ELSE WHILE RETURN BREAK
%token WHEN
%token WRITES READS
%token P_PROC_INIT
// %token AWAIT EMIT WATCHING WHEN PAR "||"
%token PAR SEQ
%token P_INIT P_LOOP
// %token P_LPAREN "((" P_RPAREN "))"
%token WITH
%token TRUE FALSE 
%token PLUS "+" MINUS "-" MUL "*" DIV "/" REM "%"
%token LE "<=" GE ">=" EQ "==" NEQ "!="
%token AND OR NOT "!"
%token CASE
%token REF "&"
%token MUT
%token ARRAY
// %token P_AND
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

%start <metadata -> (statement,(statement,expression) process_body) SailModule.methods_processes SailModule.t E.t> sailModule

%% 

let sailModule := i = import* ; l = defn* ; EOF ; {fun metadata -> mk_program metadata (ImportSet.of_list i) l}

let defn :=
| TYPE ; name = ID ; ty = preceded("=",sailtype)? ; 
    {Type {name; loc = $loc; ty} }

| STRUCT ; s_name = ID ; s_generics = generic ; s_fields = brace_del_sep_list(",", id_colon(sailtype)) ;
    {Struct {s_pos=$loc;s_name; s_generics; s_fields}}

| ENUM ; e_name = ID ; e_generics = generic ; e_injections = brace_del_sep_list(",", enum_elt) ;
    {Enum {e_pos=$loc;e_name; e_generics; e_injections}}

| METHOD ; name=ID ; generics=generic ; LPAREN ; params=separated_list(",", mutable_var(sailtype)) ; RPAREN ; rtype=returnType ; body = block ; 
    {Method [{m_proto={pos=$loc;name; generics; params; variadic=false; rtype=rtype ; extern = false}; m_body = Either.right body}]}

| EXTERN ; lib=STRING? ; protos =  delimited("{", separated_nonempty_list_opt(";", extern_sig), "}") ;
    {let protos = List.map (
        fun (sid,p) -> 
            let lib = match lib with Some s -> String.split_on_char ' ' s | None -> [] in 
            {m_proto=p; m_body=Either.left (sid,lib)}
    ) protos in Method protos}
    
| PROCESS 
    ; p_name = UID ; p_generics=generic
    ; p_params = midrule(x = process_params(separated_list(",", mutable_var(sailtype))) ; {Option.value x ~default:[]})
    ; p_shared_vars = shared_vars(located(~ = ID ; ":" ; ~ = sailtype ; <>))
    ; p_body = delimited("{", process_body, "}") ;
    {
        Process ({p_pos=$loc;p_name; p_generics; p_interface = {p_params; p_shared_vars}; p_body})
    }

let process_params(params) == ~ = parenthesized(params)? ; <>

let shared_vars(var) := 
    | (* empty *) {[],[]}
    | READS ; v = var_list(var) ; {v,[]}
    | WRITES ; v = var_list(var) ; {[],v}
    | READS ; r = var_list(var) ; "," ; WRITES ; w = var_list(var) ; {r,w}

let var_list(var) := 
    | x = var ; {[x]}
    | parenthesized(separated_list(",", var))


let process_body := 
    locals = list(id_colon(sailtype)) ; 
    init  = midrule(P_INIT ; ":" ; statement?)? ; 
    proc_init = midrule(P_PROC_INIT ; ":" ; ~ = list(located(proc_init)) ; <>)? ; 
    loop = midrule(P_LOOP ; ":" ; loop?)? ; 
    {
        let init =  Option.(join init |> value ~default:($loc,Skip)) in
        let proc_init =  Option.value proc_init ~default:[] in
        let loop = Option.join loop |> function  Some x -> x | None -> $loc,(Statement (($loc,Skip),None)) in

        {locals;init;proc_init;loop} 
    }

let proc_init := 
    | id = UID ; ":" ; "=" ; mloc = module_loc?; proc = UID 
        ; params =  midrule(p = process_params(separated_list(",", expression)); {Option.value p ~default:[]}) 
        ; (read,write) = shared_vars(located(ID)) ; { {mloc;id;proc;params;read;write} }
    | mloc = ioption(module_loc) ; id = UID 
        ; params = midrule(p = process_params(separated_list(",", expression)); {Option.value p ~default:[]}) 
        ; (read,write) = shared_vars(located(ID)) ; { {mloc;id;proc=id;params;read;write} }

let loop := 
    located(
        | ~ = statement ; ~ = pwhen ; <Statement>
        | ~ = located(UID) ; ~ = pwhen; <Run>
        | PAR  ; cond = pwhen ; "{" ;  children = separated_list(WITH,loop) ; "}" ; { PGroup {p_ty=Parallel; cond ; children} }
        | SEQ  ; cond = pwhen ; "{" ;  children = separated_list(WITH,loop) ; "}" ; { PGroup {p_ty=Sequence; cond ; children} }
    )

let pwhen == midrule(WHEN ; LPAREN ; ~= expression ; RPAREN; <>)?

let extern_sig := METHOD ; name=ID ; LPAREN ;  params=separated_list(",", mutable_var(sailtype)) ; variadic=boption(VARARGS) ; RPAREN ; rtype=returnType ; ext_name=preceded("=",STRING)? ;
        { (match ext_name with Some n -> n | None -> name),{pos=$loc; name; generics=[]; params; variadic; rtype=rtype;extern=true} }

let enum_elt :=  ~ = UID ; ~ = loption(parenthesized(separated_list(",", sailtype))) ; <>

let import := IMPORT ; mname = ID ; {{loc=$loc;mname;dir="";proc_order=1}}

let generic := loption(delimited("<", separated_list(",", UID), ">"))

let returnType := preceded(":", sailtype)? 

let mutable_var(X) := (loc,id) = located(ID) ; ":" ; mut = mut ; ty =X ; { {id;mut;loc;ty} }

let separated_nonempty_list_opt(separator, X) :=
| x = X ; separator?  ; { [ x ] }
| x = X; separator; xs = separated_nonempty_list_opt(separator, X) ; { x :: xs }



let block := located (
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
    | ~ = ioption(module_loc) ; ~ =located(ID) ; ~ = midrule(l = brace_del_sep_list(",", id_colon(expression)); 
        {List.fold_left (fun l ((ly,y),z) -> (y,(ly,z))::l) [] l}) ; <StructAlloc>
    | ~ = located(UID) ; ~ = loption(parenthesized (separated_list(",", expression))) ; <EnumAlloc>
    | ~ = ioption(module_loc) ; ~ = located(ID) ; ~ = parenthesized(separated_list (",", expression)) ; <MethodCall>
)

let id_colon(X) := ~ = located(ID) ; ":" ; ~ = X ; <>

let literal :=
| TRUE ; {LBool(true) }
| FALSE ; {LBool(false)}
| l = INT ; size = TYPE_INT?; {let size = match size with None -> 32 | Some s -> s in LInt {l;size}}
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


let block_or_statement(b) :=
    | WHILE ; ~ = parenthesized(expression) ; ~ = b ; <While>
    | LOOP ; ~ = b ; <Loop>
    | IF ; ~ = parenthesized(expression) ; ~ = b ; ~ = endrule({None}) ;  <If>
    | IF ; ~ = parenthesized(expression) ; ~ = single_statement ; ELSE ; ~ = endrule(~ = b ; <Some>) ; <If>
    | FOR ; var = ID; IN ; iterable=parenthesized(located(iterable_or_range)) ; body = b ; { For {var;iterable; body} }


let iterable_or_range :=
|  rl = INT ; "," ; rr = INT ; {
    let rl = Z.to_int rl in 
    let rr = Z.to_int rr in 
    ArrayStatic (List.init (rr - rl) (fun i -> dummy_pos,Literal (LInt {l=Z.of_int (i + rl); size=32})))
    }
| e = expression ; {snd e}


let single_statement := 
| located (
    | vardecl
    | l = expression ; "=" ; e = expression ; <Assign>
    | CASE ; ~ = parenthesized(expression) ; ~ = brace_del_sep_list(",", case) ; <Case>
    | ~ = ioption(module_loc) ; ~ = located(ID) ; ~ = parenthesized(separated_list(",", expression)) ; <Invoke>
    | RETURN ; ~ = expression? ; <Return>
    | BREAK ; <Break>
    | block_or_statement(single_statement)
    )
| block

let vardecl := VAR ; ~ = mut ; ~ = ID ; ~ = preceded(":", sailtype)? ; ~ = preceded("=",expression)? ; <DeclVar>

let brace_del_sep_list(sep,x) := delimited("{", separated_nonempty_list(sep, x), "}") 

let located(x) == ~ = x ; { ($loc,x) }

let case := separated_pair(pattern, ":", statement)

let mut := boption(MUT)

let module_loc :=  ~ = located(ID); "::" ; <> | x = located(SELF) ; "::" ; { (fst x),Constants.sail_module_self}

let parenthesized(e) == delimited("(",e,")")


let statement := 
| single_statement
| terminated(single_statement, ";")
| located (
    | ~ = left ; ~ = statement ; <Seq>
    | ~ = single_statement ; ";" ; ~ = statement ; <Seq>
)

let left := block | located (block_or_statement(block))


let pattern :=
| ~ = ID ; <PVar>
| id = UID ; {PCons (id, [])}
| ~ = UID ; ~ = delimited("(", separated_list(",", pattern), ")") ; <PCons>


let sailtype := located(
    | TYPE_BOOL ; {Bool}
    | l = TYPE_INT ; {Int l}
    | TYPE_FLOAT ; {Float}
    | TYPE_CHAR ; {Char}
    | TYPE_STRING ; {String}
    | ARRAY ; "<" ; ~ = sailtype ; ";" ; ~ = midrule(size = INT ; {Z.to_int size}) ; ">" ; <ArrayType>
    | mloc = ioption(module_loc) ; name = located(ID) ; generic_instances = instance ; {CompoundType {origin=mloc; name; generic_instances; decl_ty=None} }
    | ~ = UID ; <GenericType>
    | REF ; b = mut ; t = sailtype ; {RefType(t,b)}
)


let instance := loption(delimited("<", separated_list(",", sailtype), ">"))