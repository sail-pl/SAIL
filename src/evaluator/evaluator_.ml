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
open Common.Monad
open Common.MonadOption
open Heap
open PpEvaluator
open ErrorOfOption
open Common.TypesCommon
open SailParser.AstParser
open Intermediate
open Domain
open MonadOperator(Result)

let evalunop (u : unOp) (v : value) : value Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  match u, v with
  | Neg, VInt x -> return (VInt (-x))
  | Neg, VFloat x -> return (VFloat (-.x))
  | Not, VBool x -> return (VBool (not x))
  | _ -> throwError TypingError
 
let evalBinop (b : binOp) (v1 : value) (v2 : value) : value Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  match b, v1, v2 with
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


(*    let open Result in
    let open MonadSyntax (Result) in
    let* v = getLocation h a in
    match v with
        | Some (Either.Left v) -> getOffset v  o 
        | _ -> throwError NotAValue
*)

let getValueAt (h : heap) ((a,o) : Heap.address * offset) : (value option) Result.t =
    let open Result in
    let open MonadSyntax (Result) in
    let* content = getLocation h a in
    (match content with
        None -> return None
        | Some (Either.Left v) -> 
            let* v = getOffset v o in return (Some v)
        | Some _ -> throwError TypingError)

let setValueAt (h: heap) ((a,o) : Heap.address * offset) (w : value) : heap Result.t =
let open Result in
let open MonadSyntax (Result) in
let* v = getLocation h a in 
let* v' = match v with 
    Some (Either.Left v) -> setOffset v o w 
    | None -> return w
    | _ -> throwError NotAValue
in  setLocation h (a, Either.Left v')

let getSignalAt (h : heap) (a : Heap.address) : bool Result.t =
    let open Result in
    let open MonadSyntax (Result) in
    let* content = getLocation h a in
    (match content with
        None -> throwError InvalidSignal
        | Some (Either.Right b) ->  return b
        | Some _ -> throwError TypingError)

let setSignalAt (h : heap) (a : Heap.address) (b : bool): heap Result.t =
    let open MonadSyntax (Result) in
    setLocation h (a, Either.Right b)

let addressOfValue (v : value option) : (Heap.address * offset) Result.t= 
    let open Result in
    let open MonadSyntax (Result) in
    match v with 
    Some (VLoc (l, Owned)) -> return (l,[])    
  | Some (VLoc (l, Borrowed (o,_b))) ->  return (l,o)
  | None -> throwError NotAValue
  | _ -> throwError TypingError

let boolOfValue (v:value) : bool Result.t =
    let open Result in
    let open MonadSyntax (Result) in
    match v with 
    VBool b -> return b 
    | _ -> throwError TypingError

let rec evalL (env : env) (h :heap) (p : Intermediate.path) : (Heap.address * offset) Result.t =
  let open MonadSyntax (Result) in
  Logs.debug (fun m ->
      m "evaluate left path < %a >" Intermediate.pp_print_path p);
  match p with
  | Intermediate.Variable x -> 
        getVariable env x >>= fun a -> return (a, [])
  | Intermediate.Deref p -> 
        evalL env h p >>= getValueAt h >>= addressOfValue
  | Intermediate.StructField (e, f) ->
      let* (a, o) = evalL env h e in
      return (a, o @ [ Field f ])

let isMovable (v : value) : bool =
    match v with 
    | VLoc (_, Owned) -> true
    | VLoc (_, Borrowed (_, true)) -> true
    | VStruct (_,_) -> true 
    | VEnum (_, _) -> true
    | _ -> false

let move (h : heap) ((a,o) : Heap.address * offset) : heap Result.t =
    let open MonadSyntax (Result) in
    let* v = getValueAt h (a,o) in
    match v with 
        Some v' when isMovable v' -> setValueAt h (a,o) v' 
        | _ -> return h

let eval (env : env) (h : heap) (e : Intermediate.expression) : (value * heap) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux e h : (value * heap) Result.t =
    Logs.debug (fun m ->
        m "evaluate expression < %a >" Intermediate.pp_print_expression e);
        Logs.debug (fun m ->
            m "current environment: %a" (EvalEnv.Env.pp_t Heap.pp_address) env);
        Logs.debug (fun m -> m "current heap: %a" (Heap.pp_t pp_print_heapValue) h);
    match e with
    | Intermediate.Path p -> 
        let* (a,o) = evalL env h p in
        let* v = getValueAt h (a, o) in 
        let* h' = move h (a, o) in
        (match v with Some v -> 
        return (v,h') | None -> throwError NotAValue)
    | Literal c -> return (valueOfLiteral c, h)
    | UnOp (u, e) -> aux e h >>= fun (x, h') -> evalunop u x >>= fun y -> return (y,h')
    | BinOp (b, e1, e2) ->
        let* (x, h') = aux e1 h in 
        let* (y, h'') = aux e2 h' in
        evalBinop b x y >>= fun y -> return (y, h'')
    | StructAlloc (id, es) ->
        let* (vs, h') = foldM (fun (x, h0) (str,e) -> aux e h0 >>= fun (v,h') -> return (FieldMap.add str v x, h')) (FieldMap.empty, h) es in
        return (VStruct (id, vs), h')
    | EnumAlloc (c, es) ->
        let* (l,h) = foldLeftM (fun (x, h0) e -> aux e h0 >>= fun (v, h') -> return (v::x, h') ) ([], h) es in     
        return (VEnum (c, l), h)
    | Ref (b, p) ->
        let* (a, o) = evalL env h p in
        return (VLoc (a, Borrowed (o,b)), h)
    | Box (e) ->
        let* (v,h1) = aux e h in 
        let (a', h2) = Heap.fresh h1 in
        let* h3 = setLocation h2 (a', Either.Left v) in
        return (VLoc(a', Owned), h3)
  in
  aux e h

let rec ownedLocations (v : value) : Heap.address list = 
    match v with 
    | VLoc (a, Owned) -> [ a ]
    | VStruct (_, m) ->
        List.concat_map ownedLocations (List.map snd (FieldMap.bindings m))
    | VEnum (_, vl) -> List.concat_map ownedLocations vl
    | _ -> []

let rec deepFree (h : heap) (a : Heap.address) : heap Result.t =
    let open MonadSyntax (Result) in
    let open MonadFunctions (Result) in
        let* v = getLocation h a in 
        let* h' = free h a in
        match v with 
             Some (Either.Left v) -> dropReferencesFromValue h' v
            | _ -> return h'
and dropReferencesFromValue (h : heap) (v : value) : heap Result.t =
    let open MonadSyntax (Result) in
    let open MonadFunctions (Result) in
    foldLeftM deepFree h (ownedLocations v)

let rec filter ((v, p) : value * pattern) : (string * value) list option =
  let open MonadFunctions (M) in
  let open MonadOperator(Common.MonadOption.M) in
  match (v, p) with
  | _, PVar x -> Some [ (x, v) ]
  | VEnum (x, l), PCons (y, m) when x = y ->
      listMapM filter (List.combine l m) >>= fun l -> Some (List.concat l)
  | _ -> None

let rec freshn (h : heap) n : Heap.address list * heap =
  if n > 0 then
    let a, h' = Heap.fresh h in
    let l, h'' = freshn h' (n - 1) in
    (a :: l, h'')
  else ([], h)

let reduce (p : Intermediate.statement method_defn list) (c : command) (env : env)
    (h : heap) : (command status * frame * heap) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux c (env : env) h : (command status * frame * heap) Result.t =
    Logs.debug (fun m -> m "evaluate command < %a> " pp_command_short c);
    Logs.debug (fun m ->
        m "current environment: %a" (EvalEnv.Env.pp_t Heap.pp_address) env);
    Logs.debug (fun m -> m "current heap: %a" (Heap.pp_t pp_print_heapValue) h);
    match c with
    | DeclVar (_, x, _, None) ->
        let a, h0 = Heap.fresh h in
        return (Continue, EvalEnv.Env.singleton x a, h0)
    | DeclVar (_, x, _, Some e) ->
        let* (v, h0) = eval env h e in
        let freshAddres, heap1 = Heap.fresh h0 in
        let* h2 = setLocation heap1 (freshAddres, Either.Left v) in
        return (Continue, EvalEnv.Env.singleton x freshAddres, h2)
    | DeclSignal s ->
        let freshAddress, h0 = Heap.fresh h in
        let* h1 = setLocation h0 (freshAddress, Either.Right false) in
        return (Continue, EvalEnv.Env.singleton s freshAddress, h1)
    | Skip -> return (Continue, EvalEnv.Env.emptyFrame, h)
    | Assign (p, e) ->     (
        let* (targetAddress, targetOffset) = evalL env h p in
        let* (v, h0) = eval env h e in
        let* v0 = getValueAt h0 (targetAddress, targetOffset) in 
        let* h' = match v0 with Some v0 -> dropReferencesFromValue h0 v0 | None -> return h0 in 
        let* h'' = setValueAt h' (targetAddress, targetOffset) v in
        return (Continue, EvalEnv.Env.emptyFrame, h''))
    | Seq (c1, c2) -> (
        let* k1, bindings1, h1 = aux c1 env h in
        match k1 with
        | Continue ->
            let* env' = push env bindings1 in
            let* k2, bindings2, h2 = aux c2 env' h1 in
            return (k2, EvalEnv.Env.merge bindings1 bindings2, h2)
        | Suspend c1' -> return (Suspend (Seq (c1', c2)), bindings1, h1)
        | Ret -> return (Ret,bindings1, h1))
    | Block (c, w) -> (
        let* k, w', h' = aux c (EvalEnv.Env.activate env w) h in
        match k with
        | Suspend c' ->
            return (Suspend (Block (c', EvalEnv.Env.merge w w')), EvalEnv.Env.emptyFrame, h')
        | _ -> 
            let l = EvalEnv.Env.allValues (EvalEnv.Env.merge w w') in
            let* cleanHeap = foldLeftM (fun h a -> deepFree h a) h' l in 
            return (k, EvalEnv.Env.emptyFrame, cleanHeap)
        )
    | If (e, c1, c2) -> 
        let* (v, h0) = eval env h e in
        let* b = boolOfValue v in
            if b then aux (Block (c1, EvalEnv.Env.emptyFrame)) env h0
            else aux (Block (c2, EvalEnv.Env.emptyFrame)) env h0
    | While (e, c) -> 
        let* (v, h0) = eval env h e in
        let* b = boolOfValue v in
            if b then aux (Seq (Block (c, EvalEnv.Env.emptyFrame), While (e, c))) env h0
            else return (Continue, EvalEnv.Env.emptyFrame, h0)
    | Case (e, []) ->
        let* (v, _) = eval env h e in
        throwError (IncompletePatternMatching v)
    | Case (e, (p, c) :: pl) -> (
        let* (v, h0) = eval env h e in
        match filter (v, p) with
        | Some s ->
            let l, h' = freshn h0 (List.length s) in
            let vars = List.map fst s in
            let vals = List.map (fun x -> Either.Left (snd x)) s in
            let varmap =
              List.map (fun (x, y) -> EvalEnv.Env.singleton x y) (List.combine vars l)
            in
            let w = List.fold_left EvalEnv.Env.merge EvalEnv.Env.emptyFrame varmap in
            let locmap = List.combine l vals in
            let* h'' = foldLeftM setLocation h' locmap in
            aux (Block (c, w)) env h''
        | None -> aux (Case (e, pl)) env h)
    | Invoke (x, el) -> (
        let* (real_params,h0) = 
        foldLeftM (fun (vl,h0) e -> let* (v,h1) = eval env h0 e in return (v::vl, h1)) ([], h) el in 
        match List.find_opt (fun m -> m.m_proto.name = x) p with
        | None ->
            let* h' = ExternalsImplementation.extern h0 x real_params in
            return (Continue, EvalEnv.Env.emptyFrame, h')
        | Some callee -> (
            let formal_params = List.map fst callee.m_proto.params in
            let l, h' = freshn h0 (List.length real_params) in
            let varmap =
              List.map
                (fun (x, y) -> EvalEnv.Env.singleton x y)
                (List.combine formal_params l)
            in
            let* h'' =
              let values = List.map (fun x -> Either.Left x) real_params in
              foldLeftM setLocation h' (List.combine l values)
            in
            let w = List.fold_left EvalEnv.Env.merge EvalEnv.Env.emptyFrame varmap in
            let c = Domain.initCommand callee.m_body in
            let* r, w, h = aux (Block (c, w)) EvalEnv.Env.empty h'' in
            match r with
            | Ret -> return (Continue, w, h)
            | _ -> throwError MissingReturnStatement))
    | Return -> 
        return (Ret, EvalEnv.Env.emptyFrame, h)
    | Emit s ->
        let* a = getVariable env s in
        let* h' = setSignalAt h a true in
        return (Continue, EvalEnv.Env.emptyFrame, h')
    | When (s, c, w) -> (
        let* b = getVariable env s >>= getSignalAt h in
        if b then 
            let* k, w', h' = aux c (EvalEnv.Env.activate env w) h in
                match k with
                | Suspend c' -> return (Suspend (When (s, c', EvalEnv.Env.merge w w')), EvalEnv.Env.emptyFrame, h')
                | _ -> 
                    let l = EvalEnv.Env.allValues (EvalEnv.Env.merge w w') in
                    let* cleanHeap = foldLeftM (fun h a -> deepFree h a) h' l in 
                    return (k, EvalEnv.Env.emptyFrame, cleanHeap)
        else return (Suspend (When (s, c, w)), EvalEnv.Env.emptyFrame, h))
    | Watching (s, c, w) -> (
        let* k, w', h' = aux c (EvalEnv.Env.activate env w) h in
        match k with
        | Suspend c' ->
            return
              (Suspend (Watching (s, c', EvalEnv.Env.merge w w')), EvalEnv.Env.emptyFrame, h')
        | _ -> 
            let l = EvalEnv.Env.allValues (EvalEnv.Env.merge w w') in
            let* cleanHeap = foldLeftM (fun h a -> deepFree h a) h' l in 
            return (k, EvalEnv.Env.emptyFrame, cleanHeap))
    | Par (c1, w1, c2, w2) -> (
        let* k1, w1', h' = aux c1 (EvalEnv.Env.activate env w1) h in
        let* k2, w2', h'' = aux c2 (EvalEnv.Env.activate env w2) h' in
        match (k1, k2) with
        | Continue, Continue ->
            let l = EvalEnv.Env.allValues (EvalEnv.Env.merge w1 (EvalEnv.Env.merge w2 (EvalEnv.Env.merge w1' w2'))) in
            let* cleanHeap = foldLeftM (fun h a -> deepFree h a) h'' l in 
            return (Continue, EvalEnv.Env.emptyFrame, cleanHeap)
        | Continue, Suspend c ->
            return
              ( Suspend (Par (Skip, EvalEnv.Env.merge w1 w1', c, EvalEnv.Env.merge w2 w2')),
              EvalEnv.Env.emptyFrame,
                h'' )
        | Suspend c, Continue ->
            return
              ( Suspend (Par (c, EvalEnv.Env.merge w1 w1', Skip, EvalEnv.Env.merge w2 w2')),
                EvalEnv.Env.emptyFrame,
                h'' )
        | Suspend c1', Suspend c2' ->
            return
              ( Suspend (Par (c1', EvalEnv.Env.merge w1 w1', c2', EvalEnv.Env.merge w2 w2')),
              EvalEnv.Env.emptyFrame,
                h'' )
        | _ -> throwError ReturnStatementInProcess)
  in
  aux c env h

let reset (h : heap) : heap =
  Heap.map
    (fun x -> match x with Either.Right _ -> Either.Right false | _ -> x)
    h

let suspended (c : command) (h : heap) : bool Result.t =
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  Logs.debug (fun m -> m "todo %a" PpEvaluator.pp_print_command c);
  let rec aux c env =
    match c with
    | Block (c, w) -> aux c (EvalEnv.Env.activate env w)
    | Seq (c1, _) -> aux c1 env
    | When (s, c, w) -> (
        let* l = getVariable env s in
        let* b = getSignalAt h l in
        if b then aux c (EvalEnv.Env.activate env w) else return true)
    | Watching (_, c, w) -> aux c (EvalEnv.Env.activate env w)
    | Par (c1, w1, c2, w2) ->
        let* b1 = aux c1 (EvalEnv.Env.activate env w1) in
        let* b2 = aux c2 (EvalEnv.Env.activate env w2) in
        return (b1 && b2)
    | _ -> return false
  in aux c EvalEnv.Env.empty

let rec resume (c : command) (env : env) (h : heap) : command Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  match c with
  | Block (c, w) ->
      let* c' = resume c (EvalEnv.Env.activate env w) h in
      return (Block (c', w))
  | Seq (c1, c2) ->
      let* c1' = resume c1 env h in
      return (Seq (c1', c2))
    | When (s, c, w) ->
        let* c' = resume c (EvalEnv.Env.activate env w) h in
        return (When (s, c', w))
    | Watching (s, c, w) -> (
        let* a = getVariable env s in
        let* v = getLocation h a in
        match v with
        | Some (Either.Right b) ->
        if b then return Skip
        else
            let* c' = resume c (EvalEnv.Env.activate env w) h in
            return (Watching (s, c', w))
| _ -> throwError NotASignalState)
  | Par (c1, w1, c2, w2) ->
      let* c1' = resume c1 (EvalEnv.Env.activate env w1) h
      and* c2' = resume c2 (EvalEnv.Env.activate env w2) h in
      return (Par (c1', w1, c2', w2))
  | _ -> return c

  (* Separate the global loop from the computation of instants *)
let run (m : Intermediate.statement method_defn list) c : unit Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux c h =
    Logs.debug (fun m -> m "start of a microstep");
    let* kont, _, heapAfterReduce = reduce m c EvalEnv.Env.empty h in
    match kont with
    | Ret -> throwError ReturnStatementInProcess
    | Continue -> return ()
    | Suspend suspendedCommand ->
        let* b = suspended suspendedCommand heapAfterReduce in
        if b then 
            let _ = Logs.debug (fun m -> m "new instant") in
            let* nextCommand = resume suspendedCommand EvalEnv.Env.empty heapAfterReduce in
            let* b = suspended nextCommand (reset heapAfterReduce) in
            if b then aux nextCommand (reset heapAfterReduce)
            else
            (* The machine should freeze, waiting for external events *)
            let _ = Logs.debug (fun m -> m "no further progress") in
            return ()
        else
            aux suspendedCommand heapAfterReduce
        
  in
  aux (Block (c, EvalEnv.Env.emptyFrame)) Heap.empty

let start (m : Intermediate.statement method_defn list) (c : Intermediate.statement)
    : unit =
  match run m (Domain.initCommand c) with
  | Either.Left e ->
      Format.fprintf Format.std_formatter "ERROR : %a\n" pp_print_error e
  | Either.Right () -> ()