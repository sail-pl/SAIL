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
  | StructAlloc of l_str * expression dict
  | EnumAlloc of l_str * expression list 
  | MethodCall of l_str option *  l_str * expression list

  
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
  | For of {var: string; iterable : expression; body : statement}
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
  
module E = Error.Logger

let mk_program  (md:metadata) (imports: ImportSet.t)  l : statement SailModule.t E.t =
  let open SailModule in
  let open Monad.MonadSyntax(E) in
  let open Monad.MonadOperator(E) in
  let open Monad.MonadFunctions(E) in

  let rethrow where = E.catch (fun e -> E.throw {e with where}) in

  let rec aux = function
    | [] -> return (let e = DeclEnv.empty in DeclEnv.set_name md.name e,[],[])
    | d::l ->
      let* (e,m,p) = aux l in
        match d with
          | Type t -> 
            let+ env = DeclEnv.add_decl t.name t Type e |> rethrow t.loc
            in (env,m,p)

          | Struct d -> 
            let fields = List.sort_uniq (fun (s1,_) (s2,_) -> String.compare s1 s2) d.s_fields in
            E.throw_if (Error.make d.s_pos "duplicate fields" )
            (List.(length fields <> length d.s_fields)) >>
            let+ env = DeclEnv.add_decl d.s_name (d.s_pos, defn_to_proto (Struct d)) Struct e |> rethrow d.s_pos
            in (env,m,p)

          | Enum d -> 
            let+ env = DeclEnv.add_decl d.e_name (d.e_pos, defn_to_proto (Enum d)) Enum e |> rethrow d.e_pos
            in (env,m,p)

          | Method d -> 
            let+ env,funs = 
            ListM.fold_left (fun (e,f) d -> 
              let true_name = (match d.m_body with Left (sname,_) -> sname | Right _ -> d.m_proto.name) in
              let+ env =  DeclEnv.add_decl d.m_proto.name (d.m_proto.pos,true_name,defn_to_proto (Method d)) Method e
              in (env,d::f)
              ) (e,m) d in (env,funs,p)

          | Process d ->
            let+ env =  DeclEnv.add_decl d.p_name (d.p_pos,defn_to_proto (Process d)) Process e
            in (env,m,d::p)
  in 
  let+ (declEnv,methods,processes) = aux l in 
  let builtins = Builtins.get_builtins () in
  {md; imports; declEnv ; methods;processes;builtins}

