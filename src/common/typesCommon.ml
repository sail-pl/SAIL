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

type loc = Lexing.position

type sailtype =
  | Bool 
  | Int 
  | Float 
  | Char 
  | String
  | ArrayType of sailtype * int
  | CompoundType of string * sailtype list
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
  | Some CompoundType (x, _tl) -> sprintf "%s<todo>" x
  | Some Box(t) -> sprintf "ref<%s>" (string_of_sailtype (Some t))
  | Some RefType (t,b) -> 
      if b then sprintf "&mut %s" (string_of_sailtype (Some t))
      else sprintf "&%s" (string_of_sailtype (Some t))
  | Some GenericType(s) -> s
  | None -> "void"

type unOp = Neg | Not

type binOp = Plus | Mul | Div | Minus | Rem
           | Lt | Le | Gt | Ge | Eq | NEq | And | Or



type struct_defn = 
{  
  s_pos : loc;
  s_name : string;
  s_generics : string list;
  s_fields : (string * sailtype) list;
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
  p_interface : (string * sailtype) list * string list;
  p_body : 'a
}

type 'a method_defn =  
{
  m_pos : loc;
  m_name : string; 
  m_generics : string list;
  m_params : (string * sailtype) list;
  m_rtype : sailtype option;
  m_body : 'a
}

type 'a sailModule =
{
  name : string;
  structs : struct_defn list;
  enums : enum_defn list;
  methods : 'a method_defn list ;
  processes : 'a process_defn list
}

type moduleSignature = unit sailModule

let signatureOfModule m =
{
  name = m.name;
  structs = m.structs;
  enums = m.enums;
  methods = List.map (fun m -> {m_pos=m.m_pos;m_name=m.m_name; m_generics=m.m_generics;m_params=m.m_params;m_rtype=m.m_rtype;m_body=()}) m.methods;
  processes = List.map (fun p-> {p_pos=p.p_pos;p_name=p.p_name; p_generics=p.p_generics;p_interface=p.p_interface;p_body=()}) m.processes
}