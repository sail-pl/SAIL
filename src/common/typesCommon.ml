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

type 'a dict = (string * 'a) list

type sailtype =
  | Bool 
  | Int 
  | Float 
  | Char 
  | String
  | ArrayType of sailtype * int
  | CompoundType of {
      origin : (loc * string) option; 
      name : loc * string ; 
      generic_instances : sailtype list
    }
  | Box of sailtype
  | RefType of sailtype * bool
  | GenericType of string

type literal =
  | LBool of bool
  | LInt of int
  | LFloat of float
  | LChar of char
  | LString of string

let sailtype_of_literal = function
| LBool _ -> Bool
| LFloat _ -> Float
| LInt _ -> Int
| LChar _ -> Char
| LString _ -> String


let rec string_of_sailtype (t : sailtype option) : string =
  let open Printf in 
  match t with 
  | Some Bool -> "bool"
  | Some Int -> "int"
  | Some Float -> "float"
  | Some Char -> "char"
  | Some String -> "string"
  | Some ArrayType (t,s) -> sprintf "array<%s;%d>" (string_of_sailtype (Some t)) s
  | Some CompoundType {name=(_,x); generic_instances=[];_} -> (* empty compound type -> lookup what it binds to *) sprintf "%s" x
  | Some CompoundType {name=(_,x); generic_instances;_} -> sprintf "%s<%s>" x (String.concat ", " (List.map (fun t -> string_of_sailtype (Some t)) generic_instances))
  | Some Box(t) -> sprintf "ref<%s>" (string_of_sailtype (Some t))
  | Some RefType (t,b) -> 
      if b then sprintf "&mut %s" (string_of_sailtype (Some t))
      else sprintf "&%s" (string_of_sailtype (Some t))
  | Some GenericType(s) -> s
  | None -> "void"

type unOp = Neg | Not

type binOp = Plus | Mul | Div | Minus | Rem
           | Lt | Le | Gt | Ge | Eq | NEq | And | Or



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
  s_fields : (string * (loc * sailtype)) list;
}

type enum_defn = 
{
  e_pos : loc;
  e_name : string;
  e_generics : string list;
  e_injections :  (string * sailtype list) list;
}

type 'a process_defn = 
{
  p_pos : loc;
  p_name : string;
  p_generics : string list;
  p_interface : param list * string list;
  p_body : 'a
}

type method_sig = 
{
  pos : loc;
  name : string; 
  generics : string list;
  params : param list;
  rtype : sailtype option;
  variadic : bool;
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
  fields : (loc * sailtype) dict
}

type function_proto = 
{
  ret : sailtype option;
  args : param list;
  generics : string list;
  variadic : bool;
}

type _ decl = 
| Method : _ method_defn -> function_proto decl
| Process : _ process_defn -> function_proto decl
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
  let ret = None
  and args = fst d.p_interface
  and generics = d.p_generics
  and variadic = false in
  {ret;args;generics;variadic}
| Struct d -> {generics=d.s_generics;fields=d.s_fields}
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