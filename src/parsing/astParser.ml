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
open TypesCommon

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
  | StructAlloc of (loc * string) * expression FieldMap.t
  | EnumAlloc of (loc * string) * expression list 
  | MethodCall of (loc * string) option *  (loc * string) * expression list

  
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
  | Break of unit
  | Case of expression * (pattern * statement) list
  | Invoke of  (loc*string) option *  (loc*string) * expression list
  | Return of expression option
  | Run of (loc*string) * expression list
  | Loop of statement
  | Emit of string
  | Await of string
  | When of string * statement
  | Watching of string * statement
  | Block of statement

 
type defn =
  | Type of ty_defn
  | Struct of struct_defn
  | Enum of enum_defn
  | Method of statement method_defn list
  | Process of statement process_defn
  


let mk_program  (md:metadata) (imports: ImportSet.t)  l : statement SailModule.t =
  let open SailModule in
  let rec aux = function
    |  [] -> (DeclEnv.empty,[],[])
    | d::l ->
      let (e,m,p) = aux l in
        match d with
          | Type t -> 
            let env = DeclEnv.add_decl e t.name t Type in 
            (env,m,p)

          | Struct d -> 
            let env = DeclEnv.add_decl e d.s_name 
            (d.s_pos, {generics=d.s_generics;fields=d.s_fields}) Struct in
            (env,m,p)

          | Enum d -> 
            let env = DeclEnv.add_decl e d.e_name 
            (d.e_pos,{generics=d.e_generics;injections=d.e_injections}) Enum  in
            (env,m,p)

          | Method d -> 
            let env,funs = 
            List.fold_left (fun (e,f) d -> 
              let env = 
                let pos = d.m_proto.pos
                and true_name = (match d.m_body with Left (sname,_) -> sname | Right _ -> d.m_proto.name)
                and ret = d.m_proto.rtype 
                and args = d.m_proto.params 
                and generics = d.m_proto.generics 
                and variadic = d.m_proto.variadic in
                DeclEnv.add_decl e d.m_proto.name
                (pos,true_name,{ret;args;generics;variadic}) Method in
                (env,d::f)
              ) (e,m) d in (env,funs,p)
          | Process d ->
            let env = 
              let pos = d.p_pos
              and ret = None
              and args = fst d.p_interface
              and generics = d.p_generics
              and variadic = false in
              DeclEnv.add_decl e d.p_name
              (pos,{ret;args;generics;variadic}) Process
            in (env,m,d::p)
  in 
  let (declEnv,methods,processes) = aux l in 
  let builtins = Builtins.get_builtins () in
  {md; imports; declEnv ; methods;processes;builtins}

