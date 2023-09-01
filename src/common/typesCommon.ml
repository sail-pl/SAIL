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

module FieldMap = Map.Make (String)
module FieldSet = Set.Make (String)

type loc = Lexing.position * Lexing.position
let dummy_pos : loc = Lexing.dummy_pos,Lexing.dummy_pos

type ('i,'n) tagged_node = {tag : 'i; node : 'n}
let mk_tagged_node tag node = {tag;node}

type ('i,'v) importable = {import : 'i; value : 'v}
let mk_importable import value = {import;value}

type 'v locatable  = {loc : loc; value : 'v}
let mk_locatable loc value = {loc;value}



type 'a dict = (string * 'a) list

type l_str = string locatable

type ('m,'p,'s,'e,'t) decl_sum = M of 'm | P of 'p | S of 's | E of 'e | T of 't 


type unit_decl = (unit,unit,unit,unit,unit) decl_sum

let unit_decl_of_decl : (_,_,_,_,_) decl_sum -> unit_decl = function
| M _ ->  M ()
| P _ -> P ()
| S _ -> S ()
| E _ ->  E ()
| T _ -> T ()

let string_of_decl : (_,_,_,_,_) decl_sum -> string = function
| M _ ->  "method"
| P _ -> "process"
| S _ -> "struct"
| E _ ->  "enum"
| T _ -> "type"


type sailtype = sailtype_ locatable and sailtype_ = 
  | Bool 
  | Int of int
  | Float 
  | Char 
  | String
  | ArrayType of sailtype * int
  | CompoundType of {
      origin : l_str option;
      decl_ty : unit_decl option; 
      name : l_str ; 
      generic_instances : sailtype list
    }
  | Box of sailtype
  | RefType of sailtype * bool
  | GenericType of string

type literal =
  | LBool of bool
  | LInt of {l:Z.t;size:int}
  | LFloat of float
  | LChar of char
  | LString of string

let sailtype_of_literal = function
| LBool _ -> mk_locatable dummy_pos Bool
| LFloat _ -> mk_locatable dummy_pos Float
| LInt l -> mk_locatable dummy_pos @@ Int l.size
| LChar _ -> mk_locatable dummy_pos Char
| LString _ -> mk_locatable dummy_pos String


let rec string_of_sailtype (t : sailtype option) : string =
  let open Printf in 
  match t with 
  | Some t -> 
    begin
      match t.value with 
    | Bool -> "bool"
    | Int size -> "i" ^ string_of_int  size
    | Float -> "float"
    | Char -> "char"
    | String -> "string"
    | ArrayType (t,s) -> sprintf "array<%s;%d>" (string_of_sailtype (Some t)) s
    | CompoundType {name; generic_instances=[];_} -> (* empty compound type -> lookup what it binds to *) sprintf "%s" name.value
    | CompoundType {name; generic_instances;_} -> sprintf "%s<%s>" name.value (String.concat ", " (List.map (fun t -> string_of_sailtype (Some t)) generic_instances))
    | Box(t) -> sprintf "ref<%s>" (string_of_sailtype (Some t))
    | RefType (t,b) -> 
        if b then sprintf "&mut %s" (string_of_sailtype (Some t))
        else sprintf "&%s" (string_of_sailtype (Some t))
    | GenericType(s) -> s
    end
  | None -> "void"

type unOp = Neg | Not

type binOp = Plus | Mul | Div | Minus | Rem | Lt | Le | Gt | Ge | Eq | NEq | And | Or



type param = {
      id: string;
      mut: bool;
      loc : loc;
      ty : sailtype;
}

type struct_defn = 
{  
  s_pos : loc;
  s_name : string;
  s_generics : string list;
  s_fields : (l_str * sailtype) list;
}

type enum_defn = 
{
  e_pos : loc;
  e_name : string;
  e_generics : string list;
  e_injections :  (string * sailtype list) list;
}




type interface = 
{
  p_params: param list ; 
  p_shared_vars: (string * sailtype) locatable list * (string * sailtype) locatable list
}

type 'a process_defn = 
{
  p_pos : loc;
  p_name : string;
  p_generics : string list;
  p_interface : interface;
  p_body : 'a;
}

type 'e proc_init = {
  mloc : l_str option;
  id : string;
  proc : string;
  params : 'e list;
  read : l_str list;
  write : l_str list;
}

type method_sig = 
{
  pos : loc;
  name : string; 
  generics : string list;
  params : param list;
  rtype : sailtype option;
  variadic : bool;
  extern : bool;
}

type 'a method_defn =  
{
  m_proto : method_sig;
  m_body : (string * string list,'a) Either.t
}


type ty_defn = {
  name: string;
  ty: sailtype option; (* None means abstract type *)
  loc : loc;
}

type enum_proto = 
{
  generics : string list;
  injections : (string * sailtype list) list;
}

type struct_proto = 
{
  generics : string list;
  fields : (sailtype * int) locatable dict
}

type method_proto = 
{
  ret : sailtype option;
  args : param list;
  generics : string list;
  variadic : bool;
}

type process_proto = 
{
  read : (string * sailtype) locatable list;
  write :(string * sailtype) locatable list;
  params : param list;
  generics : string list;
}

type _ decl = 
| Method : _ method_defn -> method_proto decl
| Process : _ process_defn -> process_proto decl
| Struct : struct_defn -> struct_proto decl
| Enum : enum_defn -> enum_proto decl

let defn_to_proto (type proto) (decl: proto decl) : proto = match decl with
| Method d -> 
  let ret = d.m_proto.rtype 
  and args = d.m_proto.params 
  and generics = d.m_proto.generics 
  and variadic = d.m_proto.variadic in
  {ret;args;generics;variadic}
| Process d -> 
  let read,write = d.p_interface.p_shared_vars
  and generics = d.p_generics
  and params = d.p_interface.p_params in 
  {read;write;generics;params}
| Struct d -> {generics=d.s_generics;fields=List.mapi (fun i (n,t) -> n.value,mk_locatable n.loc (t,i)) d.s_fields}
| Enum d -> {generics=d.e_generics;injections=d.e_injections}

type import =
{
  loc : loc;
  mname : string;
  dir : string;
  proc_order: int;
}

module ImportCmp = struct type t = import let compare i1 i2 = String.compare i1.mname  i2.mname  end
module ImportSet = Set.Make(ImportCmp)

type metadata = {
  name : String.t;
  hash : Digest.t;
  libs : FieldSet.t;
  version : String.t;
}