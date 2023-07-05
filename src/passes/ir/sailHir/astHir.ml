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
  | StructRead of 'import * ('info,'import) expression * l_str
  | ArrayRead of ('info,'import) expression * ('info,'import) expression  
  | Literal of literal
  | UnOp of unOp * ('info,'import) expression
  | BinOp of binOp * ('info,'import)  expression * ('info,'import) expression
  | Ref of bool * ('info,'import) expression
  | ArrayStatic of ('info,'import) expression list
  | StructAlloc of 'import * l_str * ('info,'import) expression dict
  | EnumAlloc of l_str * ('info,'import) expression list 
  | MethodCall of l_str * 'import * ('info,'import) expression list

  

type ('info,'import,'exp) statement = {info: 'info; stmt: ('info,'import,'exp) _statement} and ('info,'import,'exp) _statement =
  | DeclVar of bool * string * sailtype option * 'exp option 
  | Skip
  | Assign of 'exp * 'exp
  | Seq of ('info,'import,'exp) statement * ('info,'import,'exp) statement
  | If of 'exp * ('info,'import,'exp) statement * ('info,'import,'exp) statement option
  | Loop of ('info,'import,'exp) statement
  | Break
  | Case of 'exp * (string * string list * ('info,'import,'exp) statement) list
  | Invoke of string option * 'import * l_str * 'exp list
  | Return of 'exp option
  (*
  | DeclSignal of string
  | Emit of string
  | Await of string
  | When of string * ('info,'import,'exp) statement
  | Watching of string * ('info,'import,'exp) statement
  | Par of ('info,'import,'exp) statement * ('info,'import,'exp) statement
  *)
  | Block of ('info,'import,'exp) statement

let buildExp info (exp: (_,_) _expression) : (_,_) expression = {info;exp}
let buildStmt info stmt : (_,_,_) statement = {info;stmt}


module Syntax = struct
  let skip = buildStmt dummy_pos Skip

  let (=) = fun l r -> buildStmt dummy_pos (Assign (l,r))

  let var (loc,id,ty) = buildStmt loc (DeclVar (true,id,Some ty,None))

  let _true = buildExp dummy_pos (Literal (LBool true))
  let _false = buildExp dummy_pos (Literal (LBool false))


  let (+) = fun l r -> buildExp dummy_pos (BinOp(Plus,l,r))
  let (%) = fun l r -> buildExp dummy_pos (BinOp(Rem,l,r))
  let (==) = fun l r -> buildExp dummy_pos (BinOp(Eq, l,r))
  
  let (&&) = fun s1 s2 -> buildStmt dummy_pos (Seq (s1,s2))


  let (!@) = fun id -> buildExp dummy_pos (Variable id)

  let (!) = fun n -> buildExp dummy_pos (Literal (LInt {l=Z.of_int n; size=32}))

  let (!!) = fun b -> buildStmt dummy_pos  (Block b)

  let _if cond _then _else = 
    let _else = match _else.stmt with Skip -> None | stmt ->  Some {_else with stmt} in 
    buildStmt dummy_pos (If (cond,_then,_else))


end