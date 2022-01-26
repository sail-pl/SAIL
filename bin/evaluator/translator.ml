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

open Ast
open Saillib.Env
open Saillib.Monoid
open Saillib.Writer
open Saillib.Monad
open Saillib.Option
open Common
open Domain

module M : Writer.Writer with type 'a t = 'a * (string * string * Domain.expression list) list  
  and type elt = (string * string * Domain.expression list) list = 
  Writer.Make(MonoidList(struct type  t = (string * string * Domain.expression list) end))

let cpt = ref 0
let freshVar () = 
  let x = !cpt in 
  let _ = cpt := !cpt +1 in 
  "_x"^(string_of_int x)

let removeCalls (e : Ast.expression) : Domain.expression *  (string * string * Domain.expression list) list = 
  let open M in
  let open MonadSyntax(M) in
  let open MonadFunctions(M) in
    let rec aux e = 
  match e with 
    | Ast.Variable x -> return (Domain.Var x)
    | Ast.Literal c -> return (Domain.Literal c)
    | Ast.UnOp(o, e) -> 
      let* x = aux e in return (Domain.UnOp(o,x))
    | Ast.BinOp(o, e1, e2) -> 
      let* e1 = aux e1 and* e2 = aux e2 in 
        return (Domain.BinOp(o,e1,e2))
    | Ast.Ref(b,e) ->
        let* e = aux e in return (Domain.Ref(b,e))
    | Ast.Deref(e) ->
        let* e = aux e in return (Domain.Deref(e))
    | Ast.ArrayRead (e1, e2) -> 
      let* e1 = aux e1 and* e2 = aux e2 in
        return (Domain.ArrayRead (e1, e2))
    | Ast.ArrayStatic (el) -> 
        let* el = listMapM aux el in 
        return (Domain.ArrayAlloc el)
    | Ast.StructRead (e,f) -> 
        let* e = aux e in return (Domain.StructRead(e,f))
    | Ast.StructAlloc (fel) -> (* change to map in AST *)
        let* el = listMapM (pairMap2 aux) fel in
        let m = List.fold_left (fun x (y,e) -> FieldMap.add y e x) FieldMap.empty el in
        return (Domain.StructAlloc(m)) 
    | Ast.EnumAlloc (x,el) ->
        let* el = listMapM aux el in 
          return (Domain.EnumAlloc(x, el))
    | Ast.MethodCall (id, el) ->
      let var = freshVar () in
      let* el = listMapM aux el in 
      let* _ = write [(var, id, el)] in
      return (Domain.Var var)
    in aux e

let mkcall ((x,m,el) : string * string * Domain.expression list) =
  [
    Domain.DeclVar (true, x, Common.Int); (* mettre le bon type*)
    Domain.Invoke(m, el@[Domain.Ref (true, Domain.Var x)]) (* modifier les méthodes *)
  ]

let seq_oflist (l : Domain.command list) : Domain.command =
  match l with 
    [] -> Skip 
    | h::t -> List.fold_left (fun x y -> Domain.Seq (x,y)) h t

let resvar = "_res"

let rec normalize (c : command) : command =
  match c with 
    | Seq(Seq(c1, c2), c3) ->  normalize (Seq (c1, Seq (c2, c3)))
    | _ -> c


let fetch_rtype (p : Ast.statement Common.program) (id : string) : Common.sailtype option =
  let open MonadSyntax(MonadOption) in
  let* m = List.find_opt (fun m -> m.m_name = id) p.methods in 
  m.m_rtype
(* A refaire avec la signature *)
    (* il faut descendre normalize dans les sous termes, sauf si seq_of_list suffit*)
let translate (p : Ast.statement Common.program) (t : Ast.statement) : Domain.command = 
  let rec aux t = 
  match t with 
      | Ast.DeclVar (b,x,t,e) -> 
        begin match e with 
            None -> Domain.DeclVar(b,x,t)
          | Some e -> 
            let (e,l) = removeCalls e in
            let n = List.concat (List.map mkcall l) in
            seq_oflist (n@[Domain.DeclVar(b,x,t); Domain.Assign(Domain.Var x, e)])
        end
      | Ast.DeclSignal (s) -> Domain.DeclSignal(s)
      | Ast.Assign (e1, e2) ->
        let (e1, l1) = removeCalls e1 in 
        let (e2, l2) = removeCalls e2 in 
        let n = List.concat (List.map mkcall (l1 @ l2)) in
        seq_oflist (n@[Domain.Assign(e1,e2)])
      | Ast.Seq [] -> Domain.Skip
      | Ast.Seq (h::t) -> 
          let h = aux  h
          and t = List.map (aux) t in
          normalize(List.fold_left (fun x y -> Seq (x, y)) h t)
      | Ast.If(e, t1, t2) -> 
          let t1 = aux t1 in
          let t2 = begin match t2 with None -> Domain.Skip | Some t2 -> aux t2 end in            
          let (e, l) = removeCalls e in 
          let m = List.concat (List.map mkcall l) in
          seq_oflist (m @ [Domain.If(e, t1, t2)])
      | Ast.While (e, t) -> 
          let t = aux t in 
          let (e, l) = removeCalls e in 
          let m = List.concat (List.map mkcall l) in
          seq_oflist (m @ [Domain.While(e, t)])
      | Ast.Case(e, pl) -> 
          let (e,l) = removeCalls e in 
          let m = List.concat (List.map mkcall l) in
            let pl = (List.map (fun (x,y) -> (x, aux  y)) pl) in
            seq_oflist (m @ [Domain.Case(e,pl)])
      | Ast.Invoke(target, m, el) -> 
        Logs.debug (fun m -> m "Here 0"); 
        let l = List.map removeCalls el in 
        let l1 = List.map fst l in 
        let l2 = List.concat (List.map snd l) in 
        let n = List.concat (List.map mkcall l2) in
        begin match fetch_rtype p m with 
            Some t -> 
              let backup = Domain.DeclVar (true, "_tmp", t) in 
              let backup_param = begin match target with 
                Some x -> [Domain.Assign(Domain.Var x, Domain.Var "_tmp")] 
              | None -> []
              end in
              let auxiliary = Domain.Ref(true, Domain.Var "_tmp") in
              Logs.debug (fun m -> m "Here 1"); (* si x = récupérer résultat *)
                seq_oflist (n @ [backup; Domain.Invoke (m, l1@[auxiliary])] @ backup_param )
            | None ->
                seq_oflist (n @ [Domain.Invoke (m, l1)])
        end
      | Return None -> Domain.Return 
      | Return (Some e) -> 
          let (e,l) = removeCalls e in
          let m = List.concat (List.map mkcall l) in 
          seq_oflist (m @ [Domain.Assign(Domain.Deref(Domain.Var resvar), e);Domain.Return])
      | Ast.Loop c -> 
        Domain.While (Literal (Common.LBool true), aux c)
      | Run _ -> failwith "processes not supported yet"
      | Ast.Emit(s) -> Domain.Emit(s)
      | When (s, c) -> Domain.When(s, aux c, Env.emptyFrame)
      | Watching (s, c) -> Domain.Watching(s, aux c, Env.emptyFrame)
      | Await (s) -> Domain.When(s, Skip,Env.emptyFrame) 
      | Par (c) -> 
          begin match List.map aux c with 
            []-> Domain.Skip
            |[c] -> c
            |c1::c2::t -> 
              List.fold_left (fun x y -> Domain.Par (x,Env.emptyFrame,y,Env.emptyFrame)) c1 (c2::t)
          end 
        in aux t

(* If the return type is non void, we add a parameter to hold the result *)
let method_translator (prg : Ast.statement program) (m : Ast.statement Common.method_defn) : Domain.command Common.method_defn =
  let params =       
    match m.m_rtype with 
      None -> m.m_params
    | Some t -> m.m_params@[(resvar, RefType(t,true))]
  in
  {
    m_name = m.m_name; 
    m_generics = m.m_generics;
    m_params = params;
    m_rtype = m.m_rtype;
    m_body = translate prg m.m_body
  }

let process_translator (prg : Ast.statement program)  (p : Ast.statement Common.process_defn) : Domain.command Common.process_defn =
  {
  p_name  = p.p_name;
  p_generics = p.p_generics;
  p_interface = p.p_interface;
  p_body = translate prg p.p_body
}

let program_translate (p : Ast.statement Common.program) : Domain.command Common.program = 
  {
    structs = p.structs;
    enums = p.enums;
    methods = List.map (method_translator p) p.methods;
    processes = List.map (process_translator p) p.processes
  }