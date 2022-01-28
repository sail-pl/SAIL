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

open Common

(* expressions are control free *)
type expression = 
    Variable of string
  | Literal of literal
  | UnOp of unOp * expression
  | BinOp of binOp * expression * expression
  | Ref of bool * expression
  | Deref of expression
  | ArrayRead of expression * expression
  | ArrayStatic of expression list
  | StructRead of expression * string
  | StructAlloc of (string * expression) list
  | EnumAlloc of (string * expression list) 
  | MethodCall of string * expression list
      
type statement =
  | DeclVar of bool * string * sailtype * expression option 
  | DeclSignal of string
  | Skip
  | Assign of expression * expression
  | Seq of statement * statement
  | Par of statement * statement
  | If of expression * statement * statement option
  | While of expression * statement
  | Case of expression * (pattern * statement) list
  | Invoke of string option * string * expression list
  | Return of expression option
  | Run of string * expression list
  | Loop of statement
  | Emit of string
  | Await of string
  | When of string * statement
  | Watching of string * statement

(* to sort definitions *)

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


  
