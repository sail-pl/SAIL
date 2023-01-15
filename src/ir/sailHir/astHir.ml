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

type 'a expression = {info: 'a ; exp:'a _expression} and 'a _expression = 
  | Variable of string 
  | Deref of 'a expression 
  | StructRead of 'a expression * string
  | ArrayRead of 'a expression * 'a expression  
  | Literal of literal
  | UnOp of unOp * 'a expression
  | BinOp of binOp * 'a expression * 'a expression
  | Ref of bool * 'a expression
  | ArrayStatic of 'a expression list
  | StructAlloc of (loc * string) * 'a expression FieldMap.t
  | EnumAlloc of (loc * string) * 'a expression list 
  

type ('i,'e) statement = {info: 'i; stmt: ('i,'e) _statement} and ('i,'e) _statement =
  | DeclVar of bool * string * sailtype option * 'e option 
  | DeclSignal of string
  | Skip
  | Assign of 'e * 'e
  | Seq of ('i,'e) statement * ('i,'e) statement
  | Par of ('i,'e) statement * ('i,'e) statement
  | If of 'e * ('i,'e) statement * ('i,'e) statement option
  | While of 'e * ('i,'e) statement
  | Break
  | Case of 'e * (string * string list * ('i,'e) statement) list
  | Invoke of string option * (loc * string) * 'e list
  | Return of 'e option
  | Run of (loc*string) * 'e list
  | Emit of string
  | Await of string
  | When of string * ('i,'e) statement
  | Watching of string * ('i,'e) statement
  | Block of ('i,'e) statement

let buildExp (info:'a) (exp:'a _expression) : 'a expression = {info;exp}
let buildStmt (info:'i) (stmt:'s) : ('i,'e) statement = {info;stmt}
