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
open Saillib.Monoid
open Saillib.Writer
open Saillib.Monad
open Saillib.Option
open Common

exception NotSupportedInCoreSail of string

(* module M : Writer.Writer with type 'a t = 'a * (string * string * Intermediate.expression list) list  
  and type elt = (string * string * Intermediate.expression list) list = 
  Writer.Make(MonoidList(struct type  t = (string * string * Intermediate.expression list) end)) *)

module M : Writer.Writer with type 'a t = 'a * Intermediate.statement list  
and type elt = Intermediate.statement list = 
Writer.Make(MonoidList(struct type  t = Intermediate.statement end))

let cpt = ref 0
let freshVar () = 
  let x = !cpt in 
  let _ = cpt := !cpt +1 in 
  "_x"^(string_of_int x)

let pathOfExpression ( e :Intermediate.expression) : Intermediate.path * Intermediate.statement list = 
  match e with 
    Path p -> (p, [])
  | _ -> 
    let x = freshVar () in (Intermediate.Variable x, [Assign (Intermediate.Variable x, e) ])

let fetch_rtype (p : Common.moduleSignature list) (id : string) : Common.sailtype option =
  let open MonadSyntax(MonadOption) in
  let l = List.concat_map (fun m-> m.methods) p in
  let* m = List.find_opt (fun m -> m.m_name = id) l in 
  m.m_rtype

let removeCalls (p : Common.moduleSignature list) (e : Ast.expression) : Intermediate.expression * Intermediate.statement list = 
  let open M in
  let open MonadSyntax(M) in
  let open MonadFunctions(M) in
    let rec aux e = 
  match e with 
    | Ast.Variable x -> return (Intermediate.Path (Intermediate.Variable x))
    | Ast.Literal c -> return (Intermediate.Literal c)
    | Ast.UnOp(o, e) -> 
      let* x = aux e in return (Intermediate.UnOp(o,x))
    | Ast.BinOp(o, e1, e2) -> 
      let* e1 = aux e1 and* e2 = aux e2 in 
        return (Intermediate.BinOp(o,e1,e2))
    | Ast.Ref(b,e) ->
      let* e = aux e in
      let (p,c) = pathOfExpression e in 
      let _ = write c in
      return (Intermediate.Ref(b, p))
    | Ast.Deref(e) ->
      let* e = aux e in
        let (p0, c) = pathOfExpression e in
        let _ = write c in
        return (Intermediate.Path (Intermediate.Deref(p0)))
    | Ast.ArrayRead(_,_) -> raise (NotSupportedInCoreSail "arrays")
    | Ast.ArrayStatic(_) -> raise (NotSupportedInCoreSail "arrays")
 (*   | Ast.ArrayRead (e1, e2) -> 
      let* e1 = aux e1 and* e2 = aux e2 in
        let (p0, c) = pathOfExpression e1 in
        let _ = write c in
        return (Intermediate.Path (Intermediate.ArrayRead (p0, e2)))
    | Ast.ArrayStatic (el) -> 
        let* el = listMapM aux el in 
        return (Intermediate.ArrayAlloc el)*)
    | Ast.StructRead (e,f) -> 
        let* e = aux e in 
        let (p0, c) = pathOfExpression e in
        let _ = write c in
          return (Intermediate.Path (Intermediate.StructField(p0,f)))
    | Ast.StructAlloc (x, fel) -> 
        let l = FieldMap.fold (fun x a y -> (x,a)::y) fel [] in    
        let* l = listMapM (pairMap2 aux) l in
        let m = List.fold_left (fun x (y,e) -> FieldMap.add y e x) FieldMap.empty l in
        return (Intermediate.StructAlloc(x,m)) 
    | Ast.EnumAlloc (x,el) ->
        let* el = listMapM aux el in 
          return (Intermediate.EnumAlloc(x, el))
    | Ast.MethodCall (id, el) ->
      if (id = "box") then
        match el with
          [e] -> let* e = aux e in return (Intermediate.Box e)
          | _ -> raise (NotSupportedInCoreSail "overloading box")
      else
      let x = freshVar () in
      let* el = listMapM aux el in 
      match fetch_rtype p id with 
      Some t ->       let* _ = write [
        Intermediate.DeclVar (true, x, t, None);
        Intermediate.Invoke(id, el@[Intermediate.Ref (true, Intermediate.Variable x)])
        ] in
      return (Intermediate.Path(Intermediate.Variable x))
      | None -> failwith ("Error in fetching return type in method : "^id)
    in aux e

let mkCall (p : Common.moduleSignature list) ((x,m,el) : string * string * Intermediate.expression list) =
  match fetch_rtype p m with 
    Some t ->
     [
      Intermediate.DeclVar (true, x, t, None); 
      Intermediate.Invoke(m, el@[Intermediate.Ref (true, Intermediate.Variable x)])
    ]
    | None -> failwith ("Error in fetching return type in method : "^m)
   
let seq_oflist (l : Intermediate.statement list) : Intermediate.statement =
  match l with 
    [] -> Skip 
    | h::t -> List.fold_left (fun x y -> Intermediate.Seq (x,y)) h t

let resvar = "_res"

let rec normalize (c : Intermediate.statement) : Intermediate.statement =
  match c with 
    | Intermediate.Seq(Intermediate.Seq(c1, c2), c3) ->  normalize (Intermediate.Seq (c1, Seq (c2, c3)))
    | _ -> c

let translate (p : Common.moduleSignature list) (t : Ast.statement) : Intermediate.statement  = 
  let rec aux t : Intermediate.statement = 
  match t with 
      | Ast.DeclVar (b,x,t,e) -> 
        begin match e with 
            None -> Intermediate.DeclVar(b,x,t,None)
          | Some e -> 
            let (e,l) = removeCalls p e in
            seq_oflist (l@[Intermediate.DeclVar(b,x,t,Some e)])
        end
      | Ast.DeclSignal (s) -> Intermediate.DeclSignal(s)
      | Ast.Skip -> Intermediate.Skip
      | Ast.Assign (e1, e2) ->
        let (e1, l1) = removeCalls p e1 in
        let (p0, l3) = pathOfExpression e1 in 
        let (e2, l2) = removeCalls p e2 in 
          seq_oflist (l1@l2@l3@[Intermediate.Assign(p0,e2)])
      | Ast.Seq (c1, c2) -> Intermediate.Seq(aux c1, aux c2)
      | Ast.If(e, t1, t2) -> 
          let t1 = aux t1 in
          let t2 = begin match t2 with None -> Intermediate.Skip | Some t2 -> aux t2 end in            
          let (e, l) = removeCalls p e in 
          seq_oflist (l @ [Intermediate.If(e, t1, t2)])
      | Ast.While (e, t) -> 
          let t = aux t in 
          let (e, l) = removeCalls p e in 
          seq_oflist (l @ [Intermediate.While(e, t)])
      | Ast.Case(e, pl) -> 
          let (e,l) = removeCalls p e in 
            let pl = (List.map (fun (x,y) -> (x, aux y) ) pl) in
            seq_oflist (l @ [Intermediate.Case(e, pl)])
      | Ast.Invoke(target, m, el) -> 
        Logs.debug (fun m -> m "Here 0"); 
        let l = List.map (removeCalls p) el in 
        let l1 = List.map fst l in 
        let l2 = List.concat (List.map snd l) in 
        begin match fetch_rtype p m with 
            Some t -> 
              let backup = Intermediate.DeclVar (true, "_tmp", t, None) in 
              let backup_param = begin match target with 
                Some x -> [Intermediate.Assign(Intermediate.Variable x, Intermediate.Path (Intermediate.Variable "_tmp"))] 
              | None -> []
              end in
              let auxiliary = Intermediate.Ref(true, Intermediate.Variable "_tmp") in
              Logs.debug (fun m -> m "Here 1"); (* si x = récupérer résultat *)
                seq_oflist (l2 @ [backup; Intermediate.Invoke (m, l1@[auxiliary])] @ backup_param )
            | None ->
                seq_oflist (l2 @ [Intermediate.Invoke (m, l1)])
        end
      | Return None -> Intermediate.Return 
      | Return (Some e) -> 
          let (e,l) = removeCalls p e in
          seq_oflist (l @ [Intermediate.Assign(Intermediate.Deref(Intermediate.Variable resvar), e);Intermediate.Return])
      | Ast.Loop c -> 
        Intermediate.While (Literal (Common.LBool true), aux c)
      | Run _ -> failwith "processes not supported yet"
      | Ast.Emit(s) -> Intermediate.Emit(s)
      | When (s, c) -> Intermediate.When(s, aux c)
      | Watching (s, c) -> Intermediate.Watching(s, aux c)
      | Await (s) -> Intermediate.When(s, Skip)
      | Par (c1, c2) -> Intermediate.Par (aux c1, aux c2)
      | Block (c) -> Intermediate.Block(aux c)
        in aux t

(* If the return type is non void, we add a parameter to hold the result *)
let method_translator (prg :  Common.moduleSignature list) (m : Ast.statement Common.method_defn) : Intermediate.statement Common.method_defn =
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

let process_translator (prg : Common.moduleSignature list)  (p : Ast.statement Common.process_defn) : Intermediate.statement Common.process_defn =
  {
  p_name  = p.p_name;
  p_generics = p.p_generics;
  p_interface = p.p_interface;
  p_body = translate prg p.p_body
}

let program_translate (prg : Common.moduleSignature list) (p : Ast.statement Common.sailModule) : Intermediate.statement Common.sailModule = 
  {
    name = p.name;
    structs = p.structs;
    enums = p.enums;
    methods = List.map (method_translator prg) p.methods;
    processes = List.map (process_translator prg) p.processes
  }