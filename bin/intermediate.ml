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

type expression =
| Variable of string
| Literal of Common.literal
| UnOp of Common.unOp * expression
| BinOp of Common.binOp * expression * expression
| ArrayAlloc of expression list
| ArrayRead of expression * expression
| StructAlloc of expression FieldMap.t
| StructRead of expression * string
| EnumAlloc of string * expression list
| Ref of bool * expression
| Deref of expression

type command =
| DeclVar of bool * string * Common.sailtype 
| DeclSignal of string
| Skip
| Assign of expression * expression
| Seq of command * command
| Block of command
| If of expression * command * command
| While of expression * command
| Case of expression * (Common.pattern * command) list
| Invoke of string * expression list
| Return
| Emit of string
| When of string * command
| Watching of string * command
| Par of command * command 