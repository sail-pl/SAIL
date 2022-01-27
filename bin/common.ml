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

open Format

module FieldMap = Map.Make (String)

type sailtype =
  | Bool 
  | Int 
  | Float 
  | Char 
  | String
  | ArrayType of sailtype
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

type unOp = Neg | Not

type binOp = Plus | Mul | Div | Minus | Rem
           | Lt | Le | Gt | Ge | Eq | NEq | And | Or

type pattern =
  | PVar of string
  | PCons of string * pattern list 

  type struct_defn = 
  {  
    s_name : string;
    s_generics : string list;
    s_fields : (string * sailtype) list;
  }

type enum_defn = 
{
  e_name : string;
  e_generics : string list;
  e_injections :  (string * sailtype list) list;
}

type 'a process_defn = 
  {
    p_name : string;
    p_generics : string list;
    p_interface : (string * sailtype) list * string list;
    p_body : 'a
  }

type 'a method_defn =  
  {
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
      methods = List.map (fun m -> {m_name=m.m_name; m_generics=m.m_generics;m_params=m.m_params;m_rtype=m.m_rtype;m_body=()}) m.methods;
      processes = List.map (fun p-> {p_name=p.p_name; p_generics=p.p_generics;p_interface=p.p_interface;p_body=()}) m.processes
    }

  let pp_comma (pf : formatter) (() : unit) : unit = Format.fprintf pf "," 
  let pp_field (pp_a : formatter -> 'a -> unit) (pf : formatter) ((x,y) : string * 'a) = 
    Format.fprintf pf "%s:%a" x pp_a y

let rec pp_pattern pf p = 
  match p with 
    | PVar x -> Format.pp_print_string pf x
    | PCons (c, pl) -> Format.fprintf pf "%s(%a)" c (Format.pp_print_list ~pp_sep:pp_comma pp_pattern) pl
    
let pp_unop pf u =
  let u = match u with Neg -> "-" | Not -> "~" in
  Format.pp_print_string pf  u 

let pp_binop pf b = 
  let b = 
    match b with 
    | Plus -> "+" | Mul -> "*" | Div -> "/" | Minus -> "-" | Rem -> "%"
    | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">=" | Eq -> "==" | NEq -> "!="
    | And -> "&&" | Or -> "||"
  in Format.pp_print_string pf b

  let pp_literal (pf : formatter) (c : literal) : unit = 
    match c with 
    | LBool (b) -> Format.fprintf pf "%b" b
    | LInt (i) -> pp_print_int pf i
    | LFloat (f) -> Format.fprintf pf "%f" f
    | LChar (c) -> Format.fprintf pf "\'%c\'" c
    | LString s -> Format.fprintf pf "\"%s\"" s 
  
  

  let rec pp_type (pf : formatter) (t : sailtype) : unit =
    match t with 
        Bool -> pp_print_string pf "bool"
      | Int -> pp_print_string pf "int"
      | Float -> pp_print_string pf "float"
      | Char -> pp_print_string pf "char"
      | String -> pp_print_string pf "string"
      | ArrayType t -> Format.fprintf pf "array<%a>" pp_type t
      | CompoundType (x, tl) -> 
          Format.fprintf pf "%s<%a>" x (pp_print_list ~pp_sep:pp_comma pp_type) tl
      | Box(t) -> Format.fprintf pf "ref<%a>" pp_type t
      | RefType (t,b) -> 
          if b then Format.fprintf pf "&mut %a" pp_type t
          else Format.fprintf pf "& %a" pp_type t
      | GenericType(s) -> pp_print_string pf s 

let pp_method (pp_a : int -> formatter -> 'a -> unit ) (pf : formatter) (m : 'a method_defn) =
  match m.m_rtype with 
  None -> 
    fprintf pf "method %s (%a) {\n%a\n}\n" 
      m.m_name 
      (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) m.m_params 
      (pp_a 1) m.m_body
  | Some t -> 
    fprintf pf "method %s (%a):%a {\n%a\n}\n" 
      m.m_name 
      (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) m.m_params 
      pp_type t
      (pp_a 1) m.m_body

let pp_process (pp_a : int -> formatter -> 'a -> unit) (pf : formatter) (p : 'a process_defn) =
  fprintf pf "process %s (-) {\n%a\n}\n" p.p_name 
  (pp_a 1) p.p_body 

let pp_program (pp_a : int -> formatter -> 'a -> unit) ((pf : formatter) : formatter) (p : 'a sailModule) = 
  List.iter (pp_method pp_a pf) p.methods;
  List.iter (pp_process pp_a pf) p.processes
      