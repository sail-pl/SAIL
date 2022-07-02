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

open Common.TypesCommon

(* expressions are control free *)
type expression = loc * expression_ and expression_ = 
  Variable of string 
  | Deref of expression 
  | StructRead of expression * string
  | ArrayRead of expression * expression  
  | Literal of literal
  | UnOp of unOp * expression
  | BinOp of binOp * expression * expression
  | Ref of bool * expression
  | ArrayStatic of expression list
  | StructAlloc of string * expression FieldMap.t
  | EnumAlloc of string * expression list 
  | MethodCall of string * expression list

  
  type pattern =
  | PVar of string
  | PCons of string * pattern list   

type statement = loc * statement_ and statement_ = 
  | DeclVar of bool * string * sailtype option * expression option 
  | DeclSignal of string
  | Skip
  | Assign of expression * expression
  | Seq of statement * statement
  | Par of statement * statement
  | If of expression * statement * statement option
  | While of expression * statement
  | Case of expression * (pattern * statement) list
  | Invoke of  string * expression list
  | Return of expression option
  | Run of string * expression list
  | Loop of statement
  | Emit of string
  | Await of string
  | When of string * statement
  | Watching of string * statement
  | Block of statement


type defn =
  | Struct of struct_defn
  | Enum of enum_defn
  | Method of statement method_defn
  | Process of statement process_defn
  | Ffi of method_sig list

let mk_program name l =
  let rec aux l =
    match l with
      [] -> ([],[],[],[],[])
    | d::l ->
      let (s,e,m,p,ext) = aux l in
        match d with
          | Struct d -> (d::s,e,m,p,ext)
          | Enum d -> (s,d::e,m,p,ext)
          | Method d -> (s,e,d::m,p,ext)
          | Process d -> (s,e,m,d::p,ext)
          | Ffi d -> (s,e,m,p,d::ext)
  in 
  let (s,e,m,p,ext) = aux l in 
    {name = name; structs = s; enums =e; methods=m; processes=p; ffi=List.flatten ext}

