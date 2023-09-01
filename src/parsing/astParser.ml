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
type expression = expression_ locatable and expression_ = 
  Variable of string 
  | Deref of expression 
  | StructRead of expression * l_str
  | ArrayRead of expression * expression  
  | Literal of literal
  | UnOp of unOp * expression
  | BinOp of binOp * expression * expression
  | Ref of bool * expression
  | ArrayStatic of expression list
  | StructAlloc of l_str option * l_str * expression locatable dict
  | EnumAlloc of l_str * expression list 
  | MethodCall of l_str option *  l_str * expression list

  
type pattern =
| PVar of string
| PCons of string * pattern list   

type statement = statement_ locatable and statement_ = 
  | DeclVar of bool * string * sailtype option * expression option
  | Skip
  | Assign of {path:expression; value:expression}
  | Seq of statement * statement
  | If of expression * statement * statement option
  | While of expression * statement
  | Break of unit
  | Case of expression * (pattern * statement) list
  | Invoke of  l_str option *  l_str * expression list
  | Return of expression option
  | Loop of statement
  | For of {var: string; iterable : expression; body : statement}
  | Block of statement

  
type pgroup_ty = Sequence | Parallel

type ('s,'e) p_statement = ('s,'e) p_statement_ locatable and ('s,'e) p_statement_ = 
  | Run of l_str * 'e option
  | Statement of 's * 'e option
  | PGroup of {p_ty : pgroup_ty  ; cond : 'e option ; children :  ('s,'e) p_statement list}

type ('s,'e) process_body = {
    locals : (l_str * sailtype) list;
    init : 's;
    proc_init : ('e proc_init locatable) list;
    loop : ('s,'e) p_statement;
}

type 'a defn =
  | Type of ty_defn
  | Struct of struct_defn
  | Enum of enum_defn 
  | Method of statement method_defn list
  | Process of 'a process_defn
  
module E = Logging.Logger

let mk_program  (md:metadata) (imports: ImportSet.t)  l : (statement, (statement,expression) process_body) SailModule.methods_processes SailModule.t E.t =
  let open SailModule in
  let open Monad.MonadSyntax(E) in
  let open Monad.MonadOperator(E) in
  let open Monad.MonadFunctions(E) in

  let rethrow where = E.(catch (fun e -> throw {e with where})) in

  let rec aux = function
    | [] -> return DeclEnv.(set_name md.name empty,[],[])
    | d::l ->
      let* e,m,p = aux l in
        match d with
          | Type t -> 
            let+ env = DeclEnv.add_decl t.name t Type e |> rethrow t.loc
            in (env,m,p)

          | Struct d -> 
            let s_fields = List.sort_uniq (fun (s1,_) (s2,_) -> String.compare s1.value s2.value) d.s_fields in
            E.throw_if Logging.(make_msg d.s_pos "duplicate fields" )
            (List.(length s_fields <> length d.s_fields)) >>= fun () -> 
            let+ env = DeclEnv.add_decl d.s_name (d.s_pos, defn_to_proto (Struct {d with s_fields})) Struct e |> rethrow d.s_pos
            in (env,m,p)

          | Enum d -> 
            let+ env = DeclEnv.add_decl d.e_name (d.e_pos, defn_to_proto (Enum d)) Enum e |> rethrow d.e_pos
            in (env,m,p)

          | Method d -> 
            
            let+ env,funs = 
            ListM.fold_left (fun (e,f) d ->
              let* () = E.throw_if Logging.(make_msg d.m_proto.pos "calling a method 'main' is not allowed") (d.m_proto.name = "main") in
              let true_name = (match d.m_body with Left (sname,_) -> sname | Right _ -> d.m_proto.name) in
              let+ env =  DeclEnv.add_decl d.m_proto.name (mk_locatable d.m_proto.pos true_name,defn_to_proto (Method d)) Method e
              in (env,d::f)
              ) (e,m) d in (env,funs,p)

          | Process d ->
            let+ env =  DeclEnv.add_decl d.p_name (d.p_pos,defn_to_proto (Process d)) Process e
            in (env,m,d::p)
  in 
  let+ declEnv,methods,processes = aux l in 
  let builtins = Builtins.get_builtins () in
  {typeEnv=Env.TypeEnv.empty; md; imports; declEnv ; body={methods;processes};builtins}

