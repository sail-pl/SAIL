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

open Parser.AstParser
open Common
open Monoid
open Writer
open Monad
open Option
open TypesCommon

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

let fetch_rtype (p : moduleSignature list) (id : string) : sailtype option =
  let open MonadSyntax(MonadOption) in
  let l = List.concat_map (fun m-> m.methods) p in
  let* m = List.find_opt (fun m -> m.m_name = id) l in 
  m.m_rtype

let removeCalls (p : moduleSignature list) (e : expression) : Intermediate.expression * Intermediate.statement list = 
  let open M in
  let open MonadSyntax(M) in
  let open MonadFunctions(M) in
    let rec aux e = 
  match e with 
    | Variable (_, x) -> return (Intermediate.Path (Intermediate.Variable x))
    | Literal (_, c) -> return (Intermediate.Literal c)
    | UnOp(_, o, e) -> 
      let* x = aux e in return (Intermediate.UnOp(o,x))
    | BinOp(_, o, e1, e2) -> 
      let* e1 = aux e1 and* e2 = aux e2 in 
        return (Intermediate.BinOp(o,e1,e2))
    | Ref(_, b,e) ->
      let* e = aux e in
      let (p,c) = pathOfExpression e in 
      let _ = write c in
      return (Intermediate.Ref(b, p))
    | Deref(_, e) ->
      let* e = aux e in
        let (p0, c) = pathOfExpression e in
        let _ = write c in
        return (Intermediate.Path (Intermediate.Deref(p0)))
    | ArrayRead(_, _,_) -> raise (NotSupportedInCoreSail "arrays")
    | ArrayStatic(_, _) -> raise (NotSupportedInCoreSail "arrays")
 (*   | Ast.ArrayRead (e1, e2) -> 
      let* e1 = aux e1 and* e2 = aux e2 in
        let (p0, c) = pathOfExpression e1 in
        let _ = write c in
        return (Intermediate.Path (Intermediate.ArrayRead (p0, e2)))
    | Ast.ArrayStatic (el) -> 
        let* el = listMapM aux el in 
        return (Intermediate.ArrayAlloc el)*)
    | StructRead (_, e,f) -> 
        let* e = aux e in 
        let (p0, c) = pathOfExpression e in
        let _ = write c in
          return (Intermediate.Path (Intermediate.StructField(p0,f)))
    | StructAlloc (_, x, fel) -> 
        let l = FieldMap.fold (fun x a y -> (x,a)::y) fel [] in    
        let* l = listMapM (pairMap2 aux) l in
        let m = List.fold_left (fun x (y,e) -> FieldMap.add y e x) FieldMap.empty l in
        return (Intermediate.StructAlloc(x,m)) 
    | EnumAlloc (_, x,el) ->
        let* el = listMapM aux el in 
          return (Intermediate.EnumAlloc(x, el))
    | MethodCall (_, id, el) ->
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

let mkCall (p : moduleSignature list) ((x,m,el) : string * string * Intermediate.expression list) =
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

let translate (p : moduleSignature list) (t : statement) : Intermediate.statement  = 
  let rec aux t : Intermediate.statement = 
  match t with 
      | DeclVar (_pos, b,x,t,e) -> 
        begin match e with 
            None -> Intermediate.DeclVar(b,x,t,None)
          | Some e -> 
            let (e,l) = removeCalls p e in
            seq_oflist (l@[Intermediate.DeclVar(b,x,t,Some e)])
        end
      | DeclSignal (_, s) -> Intermediate.DeclSignal(s)
      | Skip _ -> Intermediate.Skip
      | Assign (_, e1, e2) ->
        let (e1, l1) = removeCalls p e1 in
        let (p0, l3) = pathOfExpression e1 in 
        let (e2, l2) = removeCalls p e2 in 
          seq_oflist (l1@l2@l3@[Intermediate.Assign(p0,e2)])
      | Seq (_, c1, c2) -> Intermediate.Seq(aux c1, aux c2)
      | If(_, e, t1, t2) -> 
          let t1 = aux t1 in
          let t2 = begin match t2 with None -> Intermediate.Skip | Some t2 -> aux t2 end in            
          let (e, l) = removeCalls p e in 
          seq_oflist (l @ [Intermediate.If(e, t1, t2)])
      | While (_, e, t) -> 
          let t = aux t in 
          let (e, l) = removeCalls p e in 
          seq_oflist (l @ [Intermediate.While(e, t)])
      | Case(_, e, pl) -> 
          let (e,l) = removeCalls p e in 
            let pl = (List.map (fun (x,y) -> (x, aux y) ) pl) in
            seq_oflist (l @ [Intermediate.Case(e, pl)])
      | Invoke(_, target, m, el) -> 
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
      | Return (_, None) -> Intermediate.Return 
      | Return (_, Some e) -> 
          let (e,l) = removeCalls p e in
          seq_oflist (l @ [Intermediate.Assign(Intermediate.Deref(Intermediate.Variable resvar), e);Intermediate.Return])
      | Loop (_, c) -> 
        Intermediate.While (Literal (LBool true), aux c)
      | Run _ -> failwith "processes not supported yet"
      | Emit(_, s) -> Intermediate.Emit(s)
      | When (_, s, c) -> Intermediate.When(s, aux c)
      | Watching (_, s, c) -> Intermediate.Watching(s, aux c)
      | Await (_, s) -> Intermediate.When(s, Skip)
      | Par (_, c1, c2) -> Intermediate.Par (aux c1, aux c2)
      | Block (_, c) -> Intermediate.Block(aux c)
        in aux t

(* If the return type is non void, we add a parameter to hold the result *)
let method_translator (prg :  moduleSignature list) (m : statement method_defn) : Intermediate.statement method_defn =
  let params =       
    match m.m_rtype with 
      None -> m.m_params
    | Some t -> m.m_params@[(resvar, RefType(t,true))]
  in
  {
    m_pos = m.m_pos;
    m_name = m.m_name; 
    m_generics = m.m_generics;
    m_params = params;
    m_rtype = m.m_rtype;
    m_body = translate prg m.m_body
  }

let process_translator (prg : moduleSignature list)  (p : statement process_defn) : Intermediate.statement process_defn =
  {
  p_pos = p.p_pos;
  p_name  = p.p_name;
  p_generics = p.p_generics;
  p_interface = p.p_interface;
  p_body = translate prg p.p_body
}

let program_translate (prg : moduleSignature list) (p : statement sailModule) : Intermediate.statement sailModule = 
  {
    name = p.name;
    structs = p.structs;
    enums = p.enums;
    methods = List.map (method_translator prg) p.methods;
    processes = List.map (process_translator prg) p.processes
  }