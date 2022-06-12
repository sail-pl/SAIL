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
type expression = 
  Variable of loc * string 
  | Deref of loc * expression 
  | StructRead of loc * expression * string
  | ArrayRead of loc * expression * expression  
  | Literal of loc * literal
  | UnOp of loc * unOp * expression
  | BinOp of loc * binOp * expression * expression
  | Ref of loc * bool * expression
  | ArrayStatic of loc * expression list
  | StructAlloc of loc * string * expression FieldMap.t
  | EnumAlloc of loc * string * expression list 
  | MethodCall of loc * string * expression list
  
  type pattern =
  | PVar of string
  | PCons of string * pattern list   

type statement =
  | DeclVar of loc * bool * string * sailtype * expression option 
  | DeclSignal of loc * string
  | Skip of loc
  | Assign of loc * expression * expression
  | Seq of loc * statement * statement
  | Par of loc * statement * statement
  | If of loc * expression * statement * statement option
  | While of loc * expression * statement
  | Case of loc * expression * (pattern * statement) list
  | Invoke of loc * string option * string * expression list
  | Return of loc * expression option
  | Run of loc * string * expression list
  | Loop of loc * statement
  | Emit of loc * string
  | Await of loc * string
  | When of loc * string * statement
  | Watching of loc * string * statement
  | Block of loc * statement

type defn =
  | Struct of struct_defn
  | Enum of enum_defn
  | Method of statement method_defn
  | Process of statement process_defn

let mk_program name l =
  let rec aux l =
    match l with
      [] -> ([],[],[],[])
    | d::l ->
      let (s,e,m,p) = aux l in
        match d with
          | Struct d -> (d::s,e,m,p)
          | Enum d -> (s,d::e,m,p)
          | Method d -> (s,e,d::m,p)
          | Process d -> (s,e, m,d::p)
  in 
  let (s,e,m,p) = aux l in 
    {name = name; structs = s; enums =e; methods=m; processes=p}


  
