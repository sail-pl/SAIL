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
| StructAlloc of string * expression FieldMap.t
| StructRead of expression * string
| EnumAlloc of string * expression list
| Ref of bool * expression
| Deref of expression

type command =
| DeclVar of bool * string * Common.sailtype * expression option
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

let pp_print_expression pf e : unit =
  let rec aux pf e =
    match e with
    | Variable x -> Format.pp_print_string pf x
    | Literal c -> Format.fprintf pf "%a" Pp_common.pp_literal c
    | UnOp (op, e) -> Format.fprintf pf "%a%a" Pp_common.pp_unop op aux e
    | BinOp (op, e1, e2) ->
        Format.fprintf pf "(%a %a %a)" aux e1 Pp_common.pp_binop op aux e2
    | ArrayAlloc el ->
        Format.fprintf pf "[%a]"
          (Format.pp_print_list ~pp_sep:Pp_common.pp_comma aux)
          el
    | ArrayRead (e1, e2) -> Format.fprintf pf "%a[%a]" aux e1 aux e2
    | StructAlloc (x, m) ->
        let pp_field pf (x, y) = Format.fprintf pf "%s:%a" x aux y in
        Format.fprintf pf "%s{%a}" x
          (Format.pp_print_list ~pp_sep:Pp_common.pp_comma pp_field)
          (FieldMap.bindings m)
    | StructRead (e, f) -> Format.fprintf pf "%a.%s" aux e f
    | EnumAlloc (c, el) ->
        Format.fprintf pf "%s(%a)" c
          (Format.pp_print_list ~pp_sep:Pp_common.pp_comma aux)
          el
    | Ref (b, e) ->
        if b then Format.fprintf pf "&mut %a" aux e
        else Format.fprintf pf "& %a" aux e
    | Deref e -> Format.fprintf pf "* %a" aux e
  in
  aux pf e

  let pp_commaline (pf : Format.formatter) (() : unit) : unit = Format.fprintf pf ",\n" 


let rec pp_print_command (n : int) (pf : Format.formatter) (c : command) : unit =
  match c with
  | DeclVar (b, x, t, None) ->
      if b then Format.fprintf pf "%svar mut %s : %a;" (String.make n '\t') x Pp_common.pp_type t
      else Format.fprintf pf "%svar %s : %a;" (String.make n '\t') x Pp_common.pp_type t
  | DeclVar (b, x, t, Some e) ->
      if b then Format.fprintf pf "%svar mut %s : %a = %a;" (String.make n '\t') x Pp_common.pp_type t pp_print_expression e
      else Format.fprintf pf "%svar %s : %a = %a;" (String.make n '\t') x Pp_common.pp_type t pp_print_expression e
  | DeclSignal x -> Format.fprintf pf "%ssignal %s;"(String.make n '\t') x 
  | Skip -> Format.fprintf pf "%sskip;" (String.make n '\t')
  | Assign (e1, e2) ->
      Format.fprintf pf "%s%a = %a;" (String.make n '\t') pp_print_expression e1 pp_print_expression e2
  | Seq (c1, c2) -> Format.fprintf pf "%a\n%a " (pp_print_command n) c1 (pp_print_command n) c2
  | Block c -> Format.fprintf pf "%s{\n%a\n%s}" (String.make n '\t') (pp_print_command (n+1)) c (String.make n '\t')
  | If (e, c1, c2) ->
      Format.fprintf pf "if (%a) \n%a \n%a" pp_print_expression e (pp_print_command (n+1)) c1
        (pp_print_command (n+1)) c2
  | While (e, c) ->
      Format.fprintf pf "%swhile (%a)\n%a" (String.make n '\t') pp_print_expression e (pp_print_command (n+1)) c 
  | Case (e, pl) ->
      let pp_case (pf : Format.formatter) ((p, c) : Common.pattern * command) =
        Format.fprintf pf "%s%a:\n%a\n%s" (String.make (n +1) '\t') Pp_common.pp_pattern p (pp_print_command (n + 2)) c (String.make (n +1) '\t') 
      in
      Format.fprintf pf "%scase (%a) {\n%a\n%s}" (String.make n '\t') pp_print_expression e
         (Format.pp_print_list ~pp_sep:pp_commaline pp_case) 
        pl (String.make n '\t')
  | Invoke (m, el) ->
      Format.fprintf pf "%s%s (%a);" (String.make n '\t') m
        (Format.pp_print_list ~pp_sep:Pp_common.pp_comma pp_print_expression)
        el
  | Return -> Format.fprintf pf "%sreturn;" (String.make n '\t')
  | Emit s -> Format.fprintf pf "%semit %s;" (String.make n '\t') s
  | When (s, c) -> Format.fprintf pf "%swhen %s \n%a" (String.make n '\t')s (pp_print_command (n+1)) c
  | Watching (s, c) -> Format.fprintf pf "%swatch %s \n%a" (String.make n '\t') s (pp_print_command (n +1)) c
  | Par (c1, c2) ->
      Format.fprintf pf "%a || %a" (pp_print_command (n+1)) c1 (pp_print_command (n+1))c2