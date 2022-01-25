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
open Saillib.Monad
open Saillib.Heap 
open Saillib.Env
open Intermediate
open Domain
open Pp_evaluator

let mapM (f : 'a -> 'b option) (s : 'a FieldMap.t) : 'b FieldMap.t option =
  let s' = FieldMap.filter_map (fun _ x -> f x) s in
  if FieldMap.cardinal s = FieldMap.cardinal s' then Some s' else None

(* Semantics domain *)

let rec locationsOfValue (v : value) : Heap.address list =
  match v with
  | VArray vl -> List.concat (List.map locationsOfValue vl)
  | VStruct m ->
      List.concat
        (List.map locationsOfValue (FieldMap.fold (fun _ x y -> x :: y) m []))
  | VEnum (_, vl) -> List.concat (List.map locationsOfValue vl)
  | _ -> []

let _collect (h : heap) (l : Heap.address list) : Heap.address list option =
  let rec aux h l acc =  
  match l with 
    | [] -> Some acc
    | l::t -> 
        if List.mem l acc then aux h t acc 
        else 
          begin match Heap.fetch h l with 
          | Some (Some (Either.Left v)) -> 
            let x = locationsOfValue v in 
            aux h (x @ t) (l::acc)
          | Some (Some (Either.Right _)) -> aux h t (l::acc)
          | Some None -> aux h t (l::acc)
          | None -> None
          end 
        in aux h l []

let evalunop (u : unOp) (v : value) : value option =
  match (u, v) with
  | Neg, VInt x -> Some (VInt (-x))
  | Neg, VFloat x -> Some (VFloat (-.x))
  | Not, VBool x -> Some (VBool (not x))
  | _ -> None

let evalBinop (b : binOp) (v1 : value) (v2 : value) : value option =
  match (b, v1, v2) with
  | Plus, VInt x, VInt y -> Some (VInt (x + y))
  | Plus, VFloat x, VFloat y -> Some (VFloat (x -. y))
  | Minus, VInt x, VInt y -> Some (VInt (x - y))
  | Minus, VFloat x, VFloat y -> Some (VFloat (x -. y))
  | Mul, VInt x, VInt y -> Some (VInt (x * y))
  | Mul, VFloat x, VFloat y -> Some (VFloat (x *. y))
  | Div, VInt x, VInt y -> 
    (try Some (VInt (x / y)) with Division_by_zero -> None)
  | Div, VFloat x, VFloat y -> 
    (try Some (VFloat (x /. y)) with Division_by_zero -> None)
  | Rem, VInt x, VInt y -> Some (VInt (x mod y))
  | Lt, x, y -> Some (VBool (x < y))
  | Le, x, y -> Some (VBool (x <= y))
  | Gt, x, y -> Some (VBool (x > y))
  | Ge, x, y -> Some (VBool (x >= y))
  | Eq, x, y -> Some (VBool (x = y))
  | NEq, x, y -> Some (VBool (x <> y))
  | And, VBool x, VBool y -> Some (VBool (x && y))
  | Or, VBool x, VBool y -> Some (VBool (x || y))
  | _ -> None

let valueOfLiteral c = (* inline  *)
  match c with
  | LBool x -> VBool x | LInt x -> VInt x | LFloat x -> VFloat x
  | LChar x -> VChar x | LString x -> VString x
  
let rec evalL (env : env) (h : heap) (e : expression) : location option =
  let open MonadSyntax(MonadOption) in
    Logs.debug (fun m -> m "evaluate left value < %a >" pp_print_expression e);
  match e with
    | Var x -> 
      let* a = Env.fetchLoc env x in Some (locationOfAddress a)
    | Deref e -> 
        let* v = evalR env h e in 
        Logs.debug (fun m -> m "HERE WE ARE %a" pp_print_value v);
        begin match v with VLoc l -> Some l | _ -> None end
    | StructRead (e, f) ->
        let* (a, o) = evalL env h e in
        Some (a, o @ [ Field f ])
    | ArrayRead (e1, e2) -> (
        let* (a, o) = evalL env h e1 and* v = evalR env h e2 in
        match v with VInt n -> Some (a, o @ [ Indice n ]) | _ -> None)
    | _ ->

      None
and evalR (env : env) (h : heap) (e : expression) : value option =
  let open MonadOption in
  let open MonadSyntax(MonadOption) in 
  let open MonadFunctions(MonadOption) in
  let rec aux e =
    Logs.debug (fun m -> m "evaluate right value < %a >" pp_print_expression e);
    match e with
    | Var x -> 
        let* a = Env.fetchLoc env x in
        let* v = Heap.fetch h a in 
        begin match v with 
          | Some (Either.Left v) -> Some v
          | _ -> None
        end
    | Literal c -> Some (valueOfLiteral c)
    | UnOp (u, e) -> aux e >>= evalunop u
    | BinOp (b, e1, e2) ->
        let* x = aux e1 and* y = aux e2 in
        evalBinop b x y
    | ArrayAlloc es ->
        let* l = sequence (List.map aux es) in
        Some (VArray l)
    | ArrayRead (e1, e2) -> (
        let* v = aux e1 and* n = aux e2 in
        match (v, n) with VArray a, VInt n -> List.nth_opt a n | _ -> None)
    | StructAlloc es -> mapM aux es >>= fun x -> Some (VStruct x)
    | StructRead (e, f) -> (
        aux e >>= fun x ->
        match x with VStruct m -> FieldMap.find_opt f m | _ -> None)
    | EnumAlloc (c, es) ->
        let* vs = sequence (List.map aux es) in
        Some (VEnum (c, vs))
    | Ref (_,e) -> (* Enforce that mutability is respected *)
        let* a = evalL env h e in
        Some (VLoc a)
    | Deref e -> (
        let* v = aux e in
        match v with
        | VLoc (a, o) -> 
          begin match Heap.fetch h a with 
              Some u -> u >>= Either.find_left >>= Fun.flip readValue o
            | None -> None 
          end
        | _ -> None)
  in
  aux e


let rec filter ((v,p) : value * pattern) : (string * value) list option =
  let open MonadOption in 
  let open MonadFunctions (MonadOption) in
  match (v, p) with  
    | (_, PVar x) -> Some [(x,v)]
    | (VEnum (x, l), PCons (y, m)) when x = y ->
      (listMapM  filter (List.combine l m)) >>= 
      fun l -> Some (List.concat l)
    | _ -> None 

let rec buildEnv (l : (value * sailtype) list) (h : heap) : (location list * heap) option =
  let open MonadSyntax(MonadOption) in 
  match l with 
      [] -> Some ([], h) 
    | (VLoc l, RefType _ )::m -> 
        let* (n,h') = buildEnv m h in Some (l::n,  h') 
     | (_, RefType _)::_ -> None
    | (v, _)::m -> 
        let (a, h') = Heap.fresh h  in
        let* h' = Heap.update h' (a, Either.Left v) in   
        let* (n, h'') = buildEnv m h' in 
        Some ((a,[])::n, h'')

let rec freshn (h : heap) n : Heap.address list * heap = 
  if n > 0 then let (a,h') = Heap.fresh h in let (l,h'') = freshn h' (n-1) in (a::l,h'')
  else ([], h)

let reduce (p : command method_defn list) (c : command) (env : env) (h : heap) :
    (command result * frame * heap) option =
    let open MonadSyntax(MonadOption) in 
    let open MonadFunctions(MonadOption) in
  let rec aux c env h  : (command result * frame * heap) option = 
  Logs.debug (fun m -> m "evaluate command < %a> " pp_command_short c); 
  Logs.debug (fun m -> m "current environment: %a" (Env.pp_t Heap.pp_address) env);
  Logs.debug (fun m -> m "current heap: %a" (Heap.pp_t pp_print_heapValue) h);
  match c with
  | DeclVar (_, x, _) ->
      let a, h0 = Heap.fresh h in
      Some (Continue, Env.singleton x a, h0)
  | DeclSignal s ->
      let a, h0 = Heap.fresh h in
      let* h1 = Heap.update h0 (a, Either.Right false) in
      Some (Continue, Env.singleton s a, h1)
  | Skip -> Some (Continue, Env.emptyFrame, h)
  | Assign (e1, e2) ->
      let* (a, o) = evalL env h e1 in 
      let*  v = evalR env h e2 in
      let* u = Heap.fetch h a in
        begin match u with 
          None -> 

            let* h' = Heap.update h (a, Either.Left v) in (* plutot faire un filtrage sur le chemin et mettre à jour direct si vide*)
            Some (Continue, Env.emptyFrame, h') (* dans ce cas update value prend un chemin non vide *)
          | Some u ->
            let* v0 = Either.find_left u in
            let* v' = updateValue v0 o v in (* update value -> option value pour representer cas non initialisé *)
            
            let* h' = Heap.update h (a, Either.Left v') in
            Some (Continue, Env.emptyFrame, h')
          end
  | Seq (c1, c2) -> (
      match aux c1 env h with
      | None -> None
      | Some (Continue, w', h') -> 
        let* env' = Env.push env w' in 
        begin match aux c2 env' h' with
          None -> None  
          | Some (k, w, h'') -> Some (k, Env.merge w' w, h'')
        end
      | Some (Suspend c1', w, h') -> Some (Suspend (Seq (c1', c2)), w, h')
      | Some (Ret, w, h') -> Some (Ret, w, h'))
  | Block (c, w) -> (
      match aux c (Env.activate env w) h with
      | Some (Suspend c', w', h') -> Some (Suspend (Block (c', Env.merge w w')), Env.emptyFrame,h')
      | Some (r, _w' ,h') ->
          (* let  l = Env.allValues (Env.merge w w') in *)
          (* let* cleanHeap = drop h' l in be careful not to drop shared ref *)
          Some (r, Env.emptyFrame, h')
      | _ -> None)
  | If (e, c1, c2) -> (
      let* v = evalR env h e in
      match v with
      | VBool b -> if b then aux (Block (c1,Env.emptyFrame)) env h else aux (Block (c2,Env.emptyFrame)) env h
      | _ -> None)
  | While (e, c) -> (
      let* v = evalR env h e in
      match v with
      | VBool b -> 
        if b then 
          aux (Seq (Block (c,Env.emptyFrame), While(e,c))) env h 
        else Some (Continue, Env.emptyFrame, h)
      | _ -> None)
  | Case (_, []) -> None
  | Case (e,(p,c)::pl) -> 
    let* v = evalR env h e in 
    begin match filter (v, p) with 
        Some s -> 
          let (l, h') = freshn h (List.length s) in 
          let vars = List.map fst s in 
          let vals = List.map (fun x -> Either.Left(snd x)) s in  
          let varmap = List.map (fun(x,y) -> Env.singleton x y ) (List.combine vars l) in
          let w = List.fold_left Env.merge Env.emptyFrame varmap in 
          let locmap = List.combine l vals in 
          let* h'' = foldLeftM Heap.update h' locmap in
          aux (Block (c, w)) env h'' 
      | None -> aux (Case (e,pl)) env h
    end 
  | Invoke (x, [e]) when x = "print_string" -> 
      begin match evalR env h e with 
        Some (VString str) -> print_string str; Some  (Continue, Env.emptyFrame, h)
        | _ -> None
        end
  | Invoke (x, [e]) when x = "print_int" -> 
    begin match evalR env h e with 
      Some (VInt str) -> print_int str; Some  (Continue, Env.emptyFrame, h)
      | _ -> None
      end
  | Invoke (x, []) when x = "print_newline" -> 
    print_newline (); Some  (Continue, Env.emptyFrame, h) 
  | Invoke (x, [e1;e2]) when x = "box" -> 
      let* v = evalR env h e1 in 
      Logs.debug (fun m -> m "COCOCO"); 
      let* v' = evalR env h e2 in
      begin match v' with 
        VLoc (a,o) ->
          let (a', h') = Heap.fresh h in
          let* u = Heap.fetch h a in
          begin match u with 
          None -> 
            (* assert o = [] ?? *)
            (
              let* h'' = Heap.update h' (a, Either.Left (VLoc (a',[]))) in (* plutot faire un filtrage sur le chemin et mettre à jour direct si vide*)
              let* h''' = Heap.update h'' (a', Either.Left v) in
              Some (Continue, Env.emptyFrame, h''')) 
            (* dans ce cas update value prend un chemin non vide *)
          | Some u ->
            Logs.debug (fun m -> m "COCOCO 2"); 
            let* v0 = Either.find_left u in
            let* v' = updateValue v0 o v in (* update value -> option value pour representer cas non initialisé *)
            let* h'' = Heap.update h' (a, Either.Left (VLoc (a',[]))) in
            let* h''' = Heap.update h'' (a', Either.Left v') in
            Some (Continue, Env.emptyFrame, h''')
          end
        | _ -> None 
        end
  | Invoke (x, el) -> 
      let* callee = List.find_opt (fun m-> m.m_name = x) p in
      let formal_params = List.map fst callee.m_params in
      let* real_params = listMapM (evalR env h) el in
      let (l, h') = freshn h (List.length real_params) in
      Logs.debug (fun m -> m "HERER ");

      let varmap = List.map (fun (x,y) -> Env.singleton x y) (List.combine formal_params l) in

      let* h'' = 
        let values = List.map (fun x -> Either.Left x) real_params in
        foldLeftM (fun x y -> Heap.update x y) h' (List.combine l values)
      in 
      let w = List.fold_left Env.merge Env.emptyFrame varmap in 
      let c = callee.m_body in 
      let* (r,w,h) = aux (Block(c, w)) Env.empty h'' in 
      begin match r with Ret -> Some (Continue, w, h) | _ -> None end 
  | Return -> Some (Ret, Env.emptyFrame, h)
  | Emit (s) ->
      let* a = Env.fetchLoc env s in
      let* h' = Heap.update h (a, Either.Right true)
      in Some (Continue, Env.emptyFrame, h')
  | When (s, c, w) -> 
      let* a = Env.fetchLoc env s in (* _ is not pretty *)
      begin match Heap.fetch h a with 
        | Some (Some (Either.Right false)) -> Some (Suspend (When (s,c,w)), Env.emptyFrame, h)
        | Some (Some (Either.Right true)) -> 
          begin match aux c (Env.activate env w) h with 
            | Some (Suspend (c'), w', h') -> Some (Suspend (When(s, c',Env.merge w w')), Env.emptyFrame, h')
            | Some (k, _w', h') -> 
              (* let  l = Env.allValues (Env.merge w w') in *)
              (* let* cleanHeap = drop h' l in *)
              Some (k, Env.emptyFrame, h')
            | None -> None
          end
        | _ -> None
      end    
  | Watching (s,c,w) -> 
    begin match aux c env h with 
        | Some (Suspend (c'), w', h') -> Some (Suspend (Watching(s, c',Env.merge w w')), Env.emptyFrame, h')
        | Some (k, _w', h') -> 
          (* let  l = Env.allValues (Env.merge w w') in *)
          (* let* cleanHeap = drop h' l in *)
          Some (k, Env.emptyFrame, h')
        | None -> None
    end
  | Par (c1, w1, c2, w2) ->
    let* (k1, w1', h') = aux c1 (Env.activate env w1) h in 
    let* (k2, w2',  h'') = aux c2 (Env.activate env w2) h' in
    begin match (k1, k2) with
      | (Continue, Continue) -> 
        (* let  l = Env.allValues (Env.merge w1 (Env.merge w2 (Env.merge w1' w2'))) in *)
        (* let* cleanHeap = drop h' l in *)
        Some (Continue, Env.emptyFrame, h')
      | (Continue, Suspend(c)) -> Some (Suspend (Par (Skip, Env.merge w1 w1', c, Env.merge w2 w2')), Env.emptyFrame, h'')
      | (Suspend c, Continue) -> Some (Suspend (Par (c, Env.merge w1 w1', Skip, Env.merge w2 w2')), Env.emptyFrame, h'')
      | (Suspend c1', Suspend c2') -> 
          Some (Suspend (Par (c1', Env.merge w1 w1', c2', Env.merge w2 w2')), Env.emptyFrame, h'') 
      | _ -> None 
    end

  in aux c env h

  let rec collect (c : command) (env : env) : Heap.address list =
    match c with 
      Block(c, w) -> (Env.allValues w) @ collect c (Env.activate env w)
    | Seq (c1, _) -> collect c1 env
    | Par (c1, w1, c2, w2) -> collect c1 (Env.activate env w1) @ (Env.allValues w1)
        @ collect c2 (Env.activate env w2) @  (Env.allValues w2)
    | When (_, c, w) -> collect c (Env.activate env w) @ (Env.allValues w)
    | Watching (_, c, w) -> collect c (Env.activate env w) @ (Env.allValues w)
     | _ -> []

  let rec kill (c : command) (env : env) (h : heap): (command * Heap.address list) option =
    let open MonadSyntax(MonadOption) in
    match c with 
        Block (c, w) -> let* (c', l) = kill c (Env.activate env w) h in Some (Block (c', w), l)
       | Seq(c1, c2) -> let* (c1', l) = kill c1 env h in Some (Seq (c1', c2), l)
      | Par (c1, w1, c2, w2) -> 
          let* (c1', l1) = kill c1 (Env.activate env w1) h
          and* (c2', l2) = kill c2 (Env.activate env w2) h
          in Some (Par (c1', w1, c2', w1), l1@l2) 
      | When (s,c, w) -> let* (c',l) = kill c (Env.activate env w) h in Some (When (s, c',w), l)
      | Watching (s,c, w) -> 
          let* a = Env.fetchLoc env s in
          let* v =Heap.fetch h a in
          begin match v with 
              Some (Either.Right b) ->  
                if b then Some (Skip, collect (Watching (s,c, w)) env)
                else let* (c', l) = kill c (Env.activate env w) h in Some (When (s, c', w), l)
            | _ -> None 
          end
      | _ -> Some (c, [])

(* AAT NESXT INSTANT *)
let run m c : unit option =
  let open MonadSyntax(MonadOption) in
  let rec aux c h = 
    let t = reduce m c Env.empty h in (* None *)
    match t with 
        None -> 
          Format.printf "\nEvaluation error, please check logs\n"; None
      | Some (r, _, h') ->
          Logs.debug (fun m -> m "Enf of the instant : %a" (Heap.pp_t pp_print_heapValue) h');
          match r with 
            | Ret ->        
              failwith "Return should not occur at the process level"
            | Continue -> Some () 
            | Suspend c -> 
              let* (c', _l) = kill c Env.empty h in 
              (* let* h'' = drop h' l in  *)
              aux c' h'
  in aux (Block (c, Env.emptyFrame)) Heap.empty


