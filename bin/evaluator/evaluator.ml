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
open Saillib.Option
open Saillib.Heap
open Saillib.Env
open Domain
open Pp_evaluator
open ErrorOfOption



let mapM (f : 'a -> 'b Result.t) (s : 'a FieldMap.t) : 'b FieldMap.t Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let rec aux (l : (string * 'a) Seq.t) : (string * 'b) Seq.t Result.t =
    match l () with
    | Seq.Nil -> return (fun () -> Seq.Nil)
    | Seq.Cons ((x, a), v) -> (
        match (f a, aux v) with
        | Either.Left u, _ -> throwError u
        | Either.Right u, Either.Right l' ->
            return (fun () -> Seq.Cons ((x, u), l'))
        | Either.Right _, Either.Left l' -> throwError l')
  in
  match aux (FieldMap.to_seq s) with
  | Either.Right s -> Either.Right (FieldMap.of_seq s)
  | Either.Left e -> Either.Left e

(* Semantics domain *)

let rec locationsOfValue (v : value) : Heap.address list =
  let vl =
    match v with
    | VArray vl -> vl
    | VStruct m -> List.map snd (FieldMap.bindings m)
    | VEnum (_, vl) -> vl
    | _ -> []
  in
  List.concat_map locationsOfValue vl

let _collect (h : heap) (l : Heap.address list) : Heap.address list Result.t =
  let open MonadSyntax (Result) in
  let rec aux h l acc : Heap.address list Result.t =
    match l with
    | [] -> return acc
    | a :: t -> (
        if List.mem a acc then aux h t acc
        else
          let* v = getLocation h a in
          match v with
          | Some (Either.Left v) ->
              let x = locationsOfValue v in
              aux h (x @ t) (a :: acc)
          | Some (Either.Right _) -> aux h t (a :: acc)
          | None -> aux h t (a :: acc))
  in
  aux h l []

let evalunop (u : unOp) (v : value) : value Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  match (u, v) with
  | Neg, VInt x -> return (VInt (-x))
  | Neg, VFloat x -> return (VFloat (-.x))
  | Not, VBool x -> return (VBool (not x))
  | _ -> throwError TypingError

let evalBinop (b : binOp) (v1 : value) (v2 : value) : value Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  match (b, v1, v2) with
  | Plus, VInt x, VInt y -> return (VInt (x + y))
  | Plus, VFloat x, VFloat y -> return (VFloat (x -. y))
  | Minus, VInt x, VInt y -> return (VInt (x - y))
  | Minus, VFloat x, VFloat y -> return (VFloat (x -. y))
  | Mul, VInt x, VInt y -> return (VInt (x * y))
  | Mul, VFloat x, VFloat y -> return (VFloat (x *. y))
  | Div, VInt x, VInt y -> (
      try return (VInt (x / y))
      with Division_by_zero -> throwError Division_by_zero)
  | Div, VFloat x, VFloat y -> (
      try return (VFloat (x /. y))
      with Division_by_zero -> throwError Division_by_zero)
  | Rem, VInt x, VInt y -> return (VInt (x mod y))
  | Lt, x, y -> return (VBool (x < y))
  | Le, x, y -> return (VBool (x <= y))
  | Gt, x, y -> return (VBool (x > y))
  | Ge, x, y -> return (VBool (x >= y))
  | Eq, x, y -> return (VBool (x = y))
  | NEq, x, y -> return (VBool (x <> y))
  | And, VBool x, VBool y -> return (VBool (x && y))
  | Or, VBool x, VBool y -> return (VBool (x || y))
  | _ -> throwError TypingError

let valueOfLiteral c =
  (* inline  *)
  match c with
  | LBool x -> VBool x
  | LInt x -> VInt x
  | LFloat x -> VFloat x
  | LChar x -> VChar x
  | LString x -> VString x

let rec evalL (env : env) (h : heap) (e : Intermediate.expression) : location Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  Logs.debug (fun m -> m "evaluate left value < %a >" Intermediate.pp_print_expression e);
  match e with
  | Intermediate.Variable x ->
      let* a = getVariable env x in
      return (locationOfAddress a)
  | Intermediate.Deref e -> (
      let* v = evalR env h e in
      match v with VLoc l -> return l | _ -> throwError TypingError)
  | Intermediate.StructRead (e, f) ->
      let* a, o = evalL env h e in
      return (a, o @ [ Field f ])
  | Intermediate.ArrayRead (e1, e2) -> (
      let* a, o = evalL env h e1 and* v = evalR env h e2 in
      match v with
      | VInt n -> return (a, o @ [ Indice n ])
      | _ -> throwError TypingError)
  | _ -> throwError NotALeftValue

and evalR (env : env) (h : heap) (e : Intermediate.expression) : value Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux e =
    Logs.debug (fun m -> m "evaluate right value < %a >" Intermediate.pp_print_expression e);
    match e with
    | Intermediate.Variable x -> (
        let* a = getVariable env x in
        let* v = getLocation h a in
        match v with
        | Some (Either.Left v) -> return v
        | _ -> throwError NotAValue)
    | Literal c -> return (valueOfLiteral c)
    | UnOp (u, e) -> aux e >>= fun x -> evalunop u x
    | BinOp (b, e1, e2) ->
        let* x = aux e1 and* y = aux e2 in
        evalBinop b x y
    | ArrayAlloc es ->
        let* l = sequence (List.map aux es) in
        return (VArray l)
    | ArrayRead (e1, e2) -> (
        let* v = aux e1 and* n = aux e2 in
        match (v, n) with
        | VArray a, VInt n -> getIndex a n
        | _ -> throwError TypingError)
    | StructAlloc es -> mapM aux es >>= fun x -> return (VStruct x)
    | StructRead (e, f) -> (
        aux e >>= fun x ->
        match x with VStruct m -> getField m f | _ -> throwError TypingError)
    | EnumAlloc (c, es) ->
        let* vs = sequence (List.map aux es) in
        return (VEnum (c, vs))
    | Ref (_, e) ->
        (* Enforce that mutability is respected *)
        let* a = evalL env h e in
        return (VLoc a)
    | Deref e -> (
        let* v = aux e in
        match v with
        | VLoc (a, o) -> (
            let* a' = getLocation h a in
            match a' with
            | None -> throwError TypingError
            | Some (Either.Left v) -> getOffset v o
            | Some (Either.Right _) -> throwError TypingError)
        | _ -> throwError TypingError)
  in
  aux e

let rec filter ((v, p) : value * pattern) : (string * value) list option =
  let open MonadOption in
  let open MonadFunctions (MonadOption) in
  match (v, p) with
  | _, PVar x -> Some [ (x, v) ]
  | VEnum (x, l), PCons (y, m) when x = y ->
      listMapM filter (List.combine l m) >>= fun l -> Some (List.concat l)
  | _ -> None

let rec buildEnv (l : (value * sailtype) list) (h : heap) :
    (location list * heap) option =
  let open MonadSyntax (MonadOption) in
  match l with
  | [] -> Some ([], h)
  | (VLoc l, RefType _) :: m ->
      let* n, h' = buildEnv m h in
      Some (l :: n, h')
  | (_, RefType _) :: _ -> None
  | (v, _) :: m ->
      let a, h' = Heap.fresh h in
      let* h' = Heap.update h' (a, Either.Left v) in
      let* n, h'' = buildEnv m h' in
      Some ((a, []) :: n, h'')

let rec freshn (h : heap) n : Heap.address list * heap =
  if n > 0 then
    let a, h' = Heap.fresh h in
    let l, h'' = freshn h' (n - 1) in
    (a :: l, h'')
  else ([], h)

let reduce (p : Intermediate.command method_defn list) (c : command) (env : env) (h : heap) :
    (command status * frame * heap) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux c env h : (command status * frame * heap) Result.t =
    Logs.debug (fun m -> m "evaluate command < %a> " pp_command_short c);
    Logs.debug (fun m ->
        m "current environment: %a" (Env.pp_t Heap.pp_address) env);
    Logs.debug (fun m -> m "current heap: %a" (Heap.pp_t pp_print_heapValue) h);
    match c with
    | DeclVar (_, x, _) ->
        let a, h0 = Heap.fresh h in
        return (Continue, Env.singleton x a, h0)
    | DeclSignal s ->
        let a, h0 = Heap.fresh h in
        let* h1 = setLocation h0 (a, Either.Right false) in
        return (Continue, Env.singleton s a, h1)
    | Skip -> return (Continue, Env.emptyFrame, h)
    | Assign (e1, e2) -> (
        let* a, o = evalL env h e1 in
        let* v = evalR env h e2 in
        let* u = getLocation h a in
        match u with
        | None ->
            let* h' = setLocation h (a, Either.Left v) in
            (* plutot faire un filtrage sur le chemin et mettre à jour direct si vide*)
            return (Continue, Env.emptyFrame, h')
            (* dans ce cas update value prend un chemin non vide *)
        | Some u ->
            let* v0 = resultOfOption TypingError Either.find_left u in
            let* v' = setOffset v0 o v in
            let* h' = setLocation h (a, Either.Left v') in
            return (Continue, Env.emptyFrame, h'))
    | Seq (c1, c2) -> (
        let* k1, w1, h1 = aux c1 env h in
        match k1 with
        | Continue ->
            let* env' = push env w1 in
            let* k2, w2, h2 = aux c2 env' h1 in
            return (k2, Env.merge w1 w2, h2)
        | Suspend c1' -> return (Suspend (Seq (c1', c2)), w1, h1)
        | Ret -> return (Ret, w1, h1))
    | Block (c, w) -> (
        let* k, w', h' = aux c (Env.activate env w) h in
        match k with
        | Suspend c' ->
            return (Suspend (Block (c', Env.merge w w')), Env.emptyFrame, h')
        | _ -> return (k, Env.emptyFrame, h'))
    | If (e, c1, c2) -> (
        let* v = evalR env h e in
        match v with
        | VBool b ->
            if b then aux (Block (c1, Env.emptyFrame)) env h
            else aux (Block (c2, Env.emptyFrame)) env h
        | _ -> throwError TypingError)
    | While (e, c) -> (
        let* v = evalR env h e in
        match v with
        | VBool b ->
            if b then aux (Seq (Block (c, Env.emptyFrame), While (e, c))) env h
            else return (Continue, Env.emptyFrame, h)
        | _ -> throwError TypingError)
    | Case (e, []) -> 
      let* v = evalR env h e in 
      throwError (IncompletePatternMatching v)
    | Case (e, (p, c) :: pl) -> (
        let* v = evalR env h e in
        match filter (v, p) with
        | Some s ->
            let l, h' = freshn h (List.length s) in
            let vars = List.map fst s in
            let vals = List.map (fun x -> Either.Left (snd x)) s in
            let varmap =
              List.map (fun (x, y) -> Env.singleton x y) (List.combine vars l)
            in
            let w = List.fold_left Env.merge Env.emptyFrame varmap in
            let locmap = List.combine l vals in
            let* h'' = foldLeftM setLocation h' locmap in
            aux (Block (c, w)) env h''
        | None -> aux (Case (e, pl)) env h)
    | Invoke (x, el) -> (
      let* real_params = listMapM (evalR env h) el in
        match List.find_opt (fun m -> m.m_name = x) p with 
          None -> 
            let* h' = ExternalsImplementation.extern h x real_params in 
            return (Continue, Env.emptyFrame, h')
        | Some callee -> 
          let formal_params = List.map fst callee.m_params in
            let l, h' = freshn h (List.length real_params) in
            let varmap =
              List.map
                (fun (x, y) -> Env.singleton x y)
                (List.combine formal_params l)
            in
            let* h'' =
              let values = List.map (fun x -> Either.Left x) real_params in
              foldLeftM setLocation h' (List.combine l values)
            in
            let w = List.fold_left Env.merge Env.emptyFrame varmap in
            let c = Domain.initCommand callee.m_body in
            let* r, w, h = aux (Block (c, w)) Env.empty h'' in
            match r with
            | Ret -> return (Continue, w, h)
            | _ -> throwError MissingReturnStatement)
    | Return -> return (Ret, Env.emptyFrame, h)
    | Emit s ->
        let* a = getVariable env s in
        let* h' = setLocation h (a, Either.Right true) in
        return (Continue, Env.emptyFrame, h')
    | When (s, c, w) -> (
        let* a = getVariable env s in
        let* v = getLocation h a in
        match v with
        | Some (Either.Right false) ->
            return (Suspend (When (s, c, w)), Env.emptyFrame, h)
        | Some (Either.Right true) -> (
            let* k, w', h' = aux c (Env.activate env w) h in
            match k with
            | Suspend c' ->
                return
                  (Suspend (When (s, c', Env.merge w w')), Env.emptyFrame, h')
            | _ -> return (k, Env.emptyFrame, h')
            (* let  l = Env.allValues (Env.merge w w') in *)
            (* let* cleanHeap = drop h' l in *))
        | None -> throwError (UnitializedAddress a)
        | _ -> throwError TypingError)
    | Watching (s, c, w) -> (
        let* k, w', h' = aux c (Env.activate env w) h in
        match k with
        | Suspend c' ->
            return
              (Suspend (Watching (s, c', Env.merge w w')), Env.emptyFrame, h')
        | _ -> return (k, Env.emptyFrame, h')
        (* let  l = Env.allValues (Env.merge w w') in *)
        (* let* cleanHeap = drop h' l in *))
    | Par (c1, w1, c2, w2) -> (
        let* k1, w1', h' = aux c1 (Env.activate env w1) h in
        let* k2, w2', h'' = aux c2 (Env.activate env w2) h' in
        match (k1, k2) with
        | Continue, Continue ->
            (* let  l = Env.allValues (Env.merge w1 (Env.merge w2 (Env.merge w1' w2'))) in *)
            (* let* cleanHeap = drop h' l in *)
            return (Continue, Env.emptyFrame, h'')
        | Continue, Suspend c ->
            return
              ( Suspend (Par (Skip, Env.merge w1 w1', c, Env.merge w2 w2')),
                Env.emptyFrame,
                h'' )
        | Suspend c, Continue ->
            return
              ( Suspend (Par (c, Env.merge w1 w1', Skip, Env.merge w2 w2')),
                Env.emptyFrame,
                h'' )
        | Suspend c1', Suspend c2' ->
            return
              ( Suspend (Par (c1', Env.merge w1 w1', c2', Env.merge w2 w2')),
                Env.emptyFrame,
                h'' )
        | _ -> throwError ReturnStatementInProcess)
  in
  aux c env h

let rec collect (c : command) (env : env) : Heap.address list =
  match c with
  | Block (c, w) -> Env.allValues w @ collect c (Env.activate env w)
  | Seq (c1, _) -> collect c1 env
  | Par (c1, w1, c2, w2) ->
      collect c1 (Env.activate env w1)
      @ Env.allValues w1
      @ collect c2 (Env.activate env w2)
      @ Env.allValues w2
  | When (_, c, w) -> collect c (Env.activate env w) @ Env.allValues w
  | Watching (_, c, w) -> collect c (Env.activate env w) @ Env.allValues w
  | _ -> []

let rec kill (c : command) (env : env) (h : heap) :
    (command * Heap.address list) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  match c with
  | Block (c, w) ->
      let* c', l = kill c (Env.activate env w) h in
      return (Block (c', w), l)
  | Seq (c1, c2) ->
      let* c1', l = kill c1 env h in
      return (Seq (c1', c2), l)
  | Par (c1, w1, c2, w2) ->
      let* c1', l1 = kill c1 (Env.activate env w1) h
      and* c2', l2 = kill c2 (Env.activate env w2) h in
      return (Par (c1', w1, c2', w2), l1 @ l2)
  | When (s, c, w) ->
      let* c', l = kill c (Env.activate env w) h in
      return (When (s, c', w), l)
  | Watching (s, c, w) -> (
      let* a = getVariable env s in
      let* v = getLocation h a in
      match v with
      | Some (Either.Right b) ->
          if b then return (Skip, collect (Watching (s, c, w)) env)
          else
            let* c', l = kill c (Env.activate env w) h in
            return (Watching (s, c', w), l)
      | _ -> throwError NotASignalState)
  | _ -> return (c, [])


(* AAT NESXT INSTANT *)
let run (m : Intermediate.command method_defn list) c : unit Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux c h =
    let* kont, _, heapAfterReduce = reduce m c Env.empty h in
    Logs.debug (fun m ->
        m "End of micro step : %a" (Heap.pp_t pp_print_heapValue) heapAfterReduce);
    match kont with
    | Ret -> throwError ReturnStatementInProcess
    | Continue -> return ()
    | Suspend suspendedCommand ->
        if h = heapAfterReduce then 
      (* if suspend we must do more microsteps if signals were emitted *)
        let* nextCommand, _l = kill suspendedCommand Env.empty heapAfterReduce in
        (* let* h'' = drop h' l in  *)
        Logs.debug (fun m ->
          m "Start a new instant: %a" (Heap.pp_t pp_print_heapValue) heapAfterReduce);
        aux nextCommand heapAfterReduce
        else 
          let _ = 
            Logs.debug (fun m ->
              m "Start a new microstep : %a" (Heap.pp_t pp_print_heapValue) heapAfterReduce);

            in
          aux suspendedCommand heapAfterReduce
  in
  aux (Block (c, Env.emptyFrame)) Heap.empty

let start (m : Intermediate.command method_defn list) (c : Intermediate.command) : unit =
  match run m (Domain.initCommand c) with
  | Either.Left e ->
      Format.fprintf Format.std_formatter "ERROR : %a\n" pp_print_error e
  | Either.Right () -> ()
