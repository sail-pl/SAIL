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


type 'a expression = 
  Variable of 'a * string 
  | Deref of 'a * 'a expression 
  | StructRead of 'a * 'a expression * string
  | ArrayRead of 'a * 'a expression * 'a expression  
  | Literal of 'a * literal
  | UnOp of 'a * unOp * 'a expression
  | BinOp of 'a * binOp * 'a expression * 'a expression
  | Ref of 'a * bool * 'a expression
  | ArrayStatic of 'a * 'a expression list
  | StructAlloc of 'a * string * 'a expression FieldMap.t
  | EnumAlloc of 'a * string * 'a expression list 
  | MethodCall of 'a * string * 'a expression list
  

type 'a statement =
  | DeclVar of loc * bool * string * sailtype option * 'a option 
  | DeclSignal of loc * string
  | Skip of loc
  | Assign of loc * 'a * 'a
  | Seq of loc * 'a statement * 'a statement
  | Par of loc * 'a statement * 'a statement
  | If of loc * 'a * 'a statement * 'a statement option
  | While of loc * 'a * 'a statement
  | Case of loc * 'a * (string * string list * 'a statement) list
  | Invoke of loc * string * 'a list
  | Return of loc * 'a option
  | Run of loc * string * 'a list
  | Emit of loc * string
  | Await of loc * string
  | When of loc * string * 'a statement
  | Watching of loc * string * 'a statement
  | Block of loc * 'a statement

  
