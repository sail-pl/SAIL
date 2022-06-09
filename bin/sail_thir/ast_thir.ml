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
  | Variable of loc * sailtype * string 
  | Deref of loc * sailtype * expression 
  | StructRead of loc * sailtype * expression * string
  | ArrayRead of loc * sailtype * expression * expression  
  | Literal of loc * sailtype * literal
  | UnOp of loc * sailtype * unOp * expression
  | BinOp of loc * sailtype * binOp * expression * expression
  | Ref of loc * sailtype * bool * expression
  | ArrayStatic of loc * sailtype * expression list
  | StructAlloc of loc * sailtype * string * expression FieldMap.t
  | EnumAlloc of loc * sailtype * string * expression list 
  | MethodCall of loc * sailtype * string * expression list
  



