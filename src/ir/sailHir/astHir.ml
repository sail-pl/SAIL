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

type ('info,'import) expression = {info: 'info ; exp: ('info,'import) _expression} and ('info,'import) _expression = 
  | Variable of string 
  | Deref of ('info,'import) expression 
  | StructRead of ('info,'import) expression * string
  | ArrayRead of ('info,'import) expression * ('info,'import) expression  
  | Literal of literal
  | UnOp of unOp * ('info,'import) expression
  | BinOp of binOp * ('info,'import)  expression * ('info,'import) expression
  | Ref of bool * ('info,'import) expression
  | ArrayStatic of ('info,'import) expression list
  | StructAlloc of (loc * string) * ('info,'import) expression FieldMap.t
  | EnumAlloc of (loc * string) * ('info,'import) expression list 
  | MethodCall of (loc * string) * 'import * ('info,'import) expression list

  

type ('info,'import,'exp) statement = {info: 'info; stmt: ('info,'import,'exp) _statement} and ('info,'import,'exp) _statement =
  | DeclVar of bool * string * sailtype option * 'exp option 
  | DeclSignal of string
  | Skip
  | Assign of 'exp * 'exp
  | Seq of ('info,'import,'exp) statement * ('info,'import,'exp) statement
  | Par of ('info,'import,'exp) statement * ('info,'import,'exp) statement
  | If of 'exp * ('info,'import,'exp) statement * ('info,'import,'exp) statement option
  | While of 'exp * ('info,'import,'exp) statement
  | Break
  | Case of 'exp * (string * string list * ('info,'import,'exp) statement) list
  | Invoke of string option * 'import * (loc * string) * 'exp list
  | Return of 'exp option
  | Run of (loc*string) * 'exp list
  | Emit of string
  | Await of string
  | When of string * ('info,'import,'exp) statement
  | Watching of string * ('info,'import,'exp) statement
  | Block of ('info,'import,'exp) statement

let buildExp info (exp: (_,_) _expression) : (_,_) expression = {info;exp}
let buildStmt info stmt : (_,_,_) statement = {info;stmt}
