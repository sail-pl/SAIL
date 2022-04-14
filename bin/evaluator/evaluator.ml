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

  let foldM (f : 'a -> (string * 'b) -> 'a Result.t) (x :'a) (y : 'b FieldMap.t) : 'a Result.t =  
    let open Result in
    let open MonadSyntax (Result) in
    let rec aux (l : (string * 'b) Seq.t) : 'a Result.t =
        match l () with 
            Seq.Nil -> return x
        |   Seq.Cons ((y, a), v) -> (
                match aux v with 
                    Either.Left u -> throwError u
                |   Either.Right u ->  f u (y, a)
        )
    in match aux (FieldMap.to_seq y) with 
    | Either.Right s -> Either.Right s
    | Either.Left e -> Either.Left e 

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
  match c with
  | LBool x -> VBool x
  | LInt x -> VInt x
  | LFloat x -> VFloat x
  | LChar x -> VChar x
  | LString x -> VString x


let rec evalL (env : env) (h : heap) (e : Intermediate.path) : (location * heap) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  Logs.debug (fun m ->
      m "evaluate left value < %a >" Intermediate.pp_print_path e);
  match e with
  | Intermediate.Variable x ->
      let* a = getVariable env x in
        return ((a,[]), h)
  | Intermediate.Deref p -> (
      let* v = evalR env h p in
      match v with (VLoc (l,_k), h) -> return (l, h) | _ -> throwError TypingError)
  | Intermediate.StructField (e, f) ->
      let* ((a, o), h) = evalL env h e in
      return ((a, o @ [ Field f ]), h)
  | Intermediate.ArrayRead (e1, e2) -> (
      let* ((a, o), h) = evalL env h e1 in 
      let* (v, h') = eval env h e2 in
      match v with
      | VInt n -> return ((a, o @ [ Indice n ]), h')
      | _ -> throwError TypingError)
and locationOfPath (env : env) (h : heap) (p : Intermediate.path) : location Result.t =
        let open Result in
        let open MonadSyntax (Result) in
        match p with 
            Variable x ->   
                let* a = getVariable env x in
                return (a, [])
        |   Deref p -> 
                let* (v,_h) = evalR env h p in 
                    begin match v with 
                        VLoc (l, _k) -> return l
                    |   _ -> throwError TypingError
                    end
        |   StructField (p,f) ->
                let* (a,o) = locationOfPath env h p in 
                    return (a,(Field f)::o)
        |   ArrayRead  (p, e) ->
                let* (a,o) = locationOfPath env h p in
                let* (v,_h') = eval env h e in 
                match v with 
                    VInt n -> return (a, Indice(n)::o)
                |   _ -> throwError TypingError
and evalR (env : env) (h : heap) (e : Intermediate.path) : (value * heap) Result.t =
    let open Result in
    let open MonadSyntax (Result) in
    let rec read (h : heap) (e : Intermediate.path) : (value * heap) Result.t =
        match e with 
        | Intermediate.Variable x ->
            (
            let* a = getVariable env x in
            let* v = getLocation h a in
            match v with
            | Some (Either.Left v) -> return (v, h)
            | _ -> throwError NotAValue)
        | Intermediate.Deref p -> (
        let* (v, h') = read h p in
        match v with
        | VLoc ((a,o), _k) -> (
            let* a' = getLocation h a in
            match a' with
            | None -> throwError TypingError
            | Some (Either.Left v) -> 
                getOffset v o >>= fun x -> return (x,h')
            | Some (Either.Right _) -> throwError TypingError)
        | Moved a -> throwError (MovedPointer a)
        | _ -> throwError TypingError)
    | Intermediate.StructField (p, f) ->
        (
        read h p >>= fun (x,h) ->
        match x with
        | VStruct (_, m) ->
            let* v = getField m f in
            return (v, h)
        | _ -> throwError TypingError)
    | Intermediate.ArrayRead (p, e2) ->
        (
        let* (v, h) = read h p in 
        let* (n, h') = eval env h e2 in
        match (v, n) with
        | VArray a, VInt n -> getIndex a n >>= fun x -> return (x, h')
        | _ -> throwError TypingError)
    in let* (v,h) = read h e in return (v,h) (* HERE *)
and eval (env : env) (h : heap) (e : Intermediate.expression) : (value * heap) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux e h =
    Logs.debug (fun m ->
        m "evaluate right value < %a >" Intermediate.pp_print_expression e);
    match e with
    | Intermediate.Path p -> evalR env h p
    | Literal c -> return (valueOfLiteral c, h)
    | UnOp (u, e) -> aux e h >>= fun (x, h') -> evalunop u x >>= fun y -> return (y,h')
    | BinOp (b, e1, e2) ->
        let* (x, h') = aux e1 h in 
        let* (y, h'') = aux e2 h' in
        evalBinop b x y >>= fun y -> return (y, h'')
    | ArrayAlloc es ->
        let* (l,h) = foldLeftM (fun (x, h0) e -> aux e h0 >>= fun (v, h') -> return (v::x, h') ) ([], h) es in     
        return (VArray l, h)
    | StructAlloc (id, es) ->
        let* (vs, h') = foldM (fun (x, h0) (str,e) -> aux e h0 >>= fun (v,h') -> return (FieldMap.add str v x, h')) (FieldMap.empty, h) es in
        return (VStruct (id, vs), h')
    | EnumAlloc (c, es) ->
        let* (l,h) = foldLeftM (fun (x, h0) e -> aux e h0 >>= fun (v, h') -> return (v::x, h') ) ([], h) es in     
        return (VEnum (c, l), h)
    | Ref (_, p) ->
        let* ((a, o), h') = evalL env h p in
        return (VLoc ((a,o),Borrowed true), h')
  in
  aux e h

(*let rec locationsOfValue (v : value) : Heap.address list =
    match v with
    | VLoc (a, _,_) -> [ a ]
    | VArray vl -> List.concat_map locationsOfValue vl
    | VStruct (_, m) ->
        List.concat_map locationsOfValue (List.map snd (FieldMap.bindings m))
    | VEnum (_, vl) -> List.concat_map locationsOfValue vl
    | _ -> []*)


let rec erasePointerInValue (a : Heap.address) (v : value)  : value =
    match v with 
    | VLoc ((b, _), Owned) when a = b -> Moved a
    | VArray vl -> VArray (List.map (erasePointerInValue a) vl)
    | VStruct (c, m) ->
        VStruct (c, FieldMap.map (erasePointerInValue a) m)
    | VEnum (c, vl) -> VEnum (c, List.map (erasePointerInValue a) vl)
    | _ -> v

let erasePointerInHeap (h : heap) (a : Heap.address) : heap =  
Heap.map (fun v -> 
    match v with 
        Either.Left u -> Either.Left (erasePointerInValue a u)
        | _ -> v
    ) h

let rec ownedLocations (v : value) : Heap.address list = 
    match v with 
    | VLoc ((a, _), Owned) -> [ a ]
    | VArray vl -> List.concat_map ownedLocations vl
    | VStruct (_, m) ->
        List.concat_map ownedLocations (List.map snd (FieldMap.bindings m))
    | VEnum (_, vl) -> List.concat_map ownedLocations vl
    | _ -> []
(* owned locations are always pure (root) *)
(* x = y.f , this is moving the content of (a,f) belongs to x, not x.f*)
(* drop value, *)
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
    foldLeftM deepFree h (ownedLocations v) (* should only free owner locations *)

let rec filter ((v, p) : value * pattern) : (string * value) list option =
  let open MonadOption in
  let open MonadFunctions (MonadOption) in
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

(* When dropping a value, we get all adresses occuring in it *)

let rec nonLinear l =
    match l with 
    [] -> false
    | h::t -> nonLinear t || List.mem h t
(* 
let linearEvalR env h e = 
    let open Result in  
    let open MonadSyntax (Result) in
    let open MonadFunctions (Result) in
    let* v = evalR env h e in
    let locs = ownedLocations v in 
    if nonLinear locs 
        then throwError (NonLinearPointer) 
    else 
        let h0 = List.fold_left (fun h a -> erasePointerInHeap h a) h locs in
        return (v, h0) *)
(* 
let linearlistEvalR env h el = 
    let open Result in  
    let open MonadSyntax (Result) in
    let open MonadFunctions (Result) in
    let* vl =  listMapM (evalR env h) el in
    let locs = List.concat_map ownedLocations vl in
    if nonLinear locs 
        then throwError (NonLinearPointer) 
    else 
        let h0 = List.fold_left (fun h a -> erasePointerInHeap h a) h locs in
        return (vl, h0) *)

(* let moveFromValue h v =
        let locs = ownedLocations v in 
        List.fold_left (fun h a -> erasePointerInHeap h a) h locs

let moveFromListValue h vl =
    let locs = List.concat_map ownedLocations vl in 
    List.fold_left (fun h a -> erasePointerInHeap h a) h locs *)
    
(* If we remove the move semantics, think to make the drop function not fail
    on desalocation of undefined addresses
    Be ware that after the first desalocation, the memory location can be reused.
    Then if one occurence remains the gc may perform a faulty desalocation.
     *)

let reduce (p : Intermediate.statement method_defn list) (c : command) (env : env)
    (h : heap) : (command status * frame * heap) Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux c (env : env) h : (command status * frame * heap) Result.t =
    Logs.debug (fun m -> m "evaluate command < %a> " pp_command_short c);
    Logs.debug (fun m ->
        m "current environment: %a" (Env.pp_t Heap.pp_address) env);
    Logs.debug (fun m -> m "current heap: %a" (Heap.pp_t pp_print_heapValue) h);
    match c with
    | DeclVar (_, x, _, None) ->
        let a, h0 = Heap.fresh h in
        return (Continue, Env.singleton x a, h0)
    | DeclVar (_, x, _, Some e) ->
        let* (v, h0) = eval env h e in
        let freshAddres, heap1 = Heap.fresh h0 in
        let* h2 = setLocation heap1 (freshAddres, Either.Left v) in
        return (Continue, Env.singleton x freshAddres, h2)
    | DeclSignal s ->
        let freshAddress, h0 = Heap.fresh h in
        let* h1 = setLocation h0 (freshAddress, Either.Right false) in
        return (Continue, Env.singleton s freshAddress, h1)
    | Skip -> return (Continue, Env.emptyFrame, h)
    | Stop -> return (Continue, Env.emptyFrame, h)
    | Assign (p, e2) -> (
        let* ((targetAddress, targetOffset), h') = evalL env h p in
        let* oldValue = getLocation h targetAddress in
        let* (newValue, h0) = eval env h' e2 in
        match oldValue with
        | None ->
            if targetOffset = [] then 
                let* h' = setLocation h0 (targetAddress, Either.Left newValue) in
                return (Continue, Env.emptyFrame, h')
            else throwError (UnitializedAddress targetAddress)
        | Some (Either.Left oldValue) ->
            let* h' = getOffset oldValue targetOffset >>= dropReferencesFromValue h0 in
            let* v' = setOffset oldValue targetOffset newValue in
            let* h'' = setLocation h' (targetAddress, Either.Left v') in
            return (Continue, Env.emptyFrame, h'')
        | Some _ -> throwError TypingError)
    | Seq (c1, c2) -> (
        let* k1, bindings1, h1 = aux c1 env h in
        match k1 with
        | Continue ->
            let* env' = push env bindings1 in
            let* k2, bindings2, h2 = aux c2 env' h1 in
            return (k2, Env.merge bindings1 bindings2, h2)
        | Suspend c1' -> return (Suspend (Seq (c1', c2)), bindings1, h1)
        | Ret -> return (Ret,bindings1, h1))
    | Block (c, w) -> (
        let* k, w', h' = aux c (Env.activate env w) h in
        match k with
        | Suspend c' ->
            return (Suspend (Block (c', Env.merge w w')), Env.emptyFrame, h')
        | _ -> 
            let l = Env.allValues (Env.merge w w') in
            let* cleanHeap = foldLeftM (fun h a -> deepFree h a) h' l in 
            return (k, Env.emptyFrame, cleanHeap)
        )
    | If (e, c1, c2) -> (
        let* (v, h0) = eval env h e in
        match v with
        | VBool b ->
            if b then aux (Block (c1, Env.emptyFrame)) env h0
            else aux (Block (c2, Env.emptyFrame)) env h0
        | _ -> throwError TypingError)
    | While (e, c) -> (
        let* (v, h0) = eval env h e in
        match v with
        | VBool b ->
            if b then aux (Seq (Block (c, Env.emptyFrame), While (e, c))) env h0
            else return (Continue, Env.emptyFrame, h0)
        | _ -> throwError TypingError)
    | Case (e, []) ->
        let* (v, _) = eval env h e in
        throwError (IncompletePatternMatching v)
    | Case (e, (p, c) :: pl) -> ( (* MOVE *)
        let* (v, h0) = eval env h e in
        match filter (v, p) with
        | Some s ->
            let l, h' = freshn h0 (List.length s) in
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
        let* (real_params,h0) = 
        foldLeftM (fun (vl,h0) e -> let* (v,h1) = eval env h0 e in return (v::vl, h1)) ([], h) el in 
        match List.find_opt (fun m -> m.m_name = x) p with
        | None ->
            let* h' = ExternalsImplementation.extern h0 x real_params in
            return (Continue, Env.emptyFrame, h')
        | Some callee -> (
            let formal_params = List.map fst callee.m_params in
            let l, h' = freshn h0 (List.length real_params) in
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
            | _ -> throwError MissingReturnStatement))
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
            (* let  l = Env.allValues (Env.merge w w') in
               let* l' = collect h' l in
               let* cleanHeap = foldLeftM ErrorOfOption.free h' (l') in
                 return (k, Env.emptyFrame, cleanHeap) *))
        | None -> throwError (UnitializedAddress a)
        | _ -> throwError TypingError)
    | Watching (s, c, w) -> (
        let* k, w', h' = aux c (Env.activate env w) h in
        match k with
        | Suspend c' ->
            return
              (Suspend (Watching (s, c', Env.merge w w')), Env.emptyFrame, h')
        | _ -> return (k, Env.emptyFrame, h')
        (* let  l = Env.allValues (Env.merge w w') in
           let* l' = collect h' l in
           let* cleanHeap = foldLeftM ErrorOfOption.free h' (l') in
             return (k, Env.emptyFrame, cleanHeap) *))
    | Par (c1, w1, c2, w2) -> (
        let* k1, w1', h' = aux c1 (Env.activate env w1) h in
        let* k2, w2', h'' = aux c2 (Env.activate env w2) h' in
        match (k1, k2) with
        | Continue, Continue ->
            return (Continue, Env.emptyFrame, h'')
            (* let  l = Env.allValues (Env.merge w1 (Env.merge w2 (Env.merge w1' w2'))) in
               let* l' = collect h' l in
               let* cleanHeap = foldLeftM ErrorOfOption.free h' (l') in
                 return (Continue, Env.emptyFrame, cleanHeap) *)
        | Continue, Suspend c ->
            return
              ( Suspend (Par (Stop, Env.merge w1 w1', c, Env.merge w2 w2')),
                Env.emptyFrame,
                h'' )
        | Suspend c, Continue ->
            return
              ( Suspend (Par (c, Env.merge w1 w1', Stop, Env.merge w2 w2')),
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

let reset (h : heap) : heap =
  Heap.map
    (fun x -> match x with Either.Right _ -> Either.Right false | _ -> x)
    h

let canProgress (c : command) (h : heap) : bool Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  Logs.debug (fun m -> m "todo %a" pp_print_command c);
  let rec aux c env =
    match c with
    | Block (c, w) -> aux c (Env.activate env w)
    | Seq (c1, _) -> aux c1 env
    | Par (c1, w1, c2, w2) ->
        let* b1 = aux c1 (Env.activate env w1) in
        let* b2 = aux c2 (Env.activate env w2) in
        return (b1 || b2)
    | When (s, c, w) -> (
        let* l = getVariable env s in
        let* v = getLocation h l in
        match v with
        | None -> throwError (UndefinedAddress l)
        | Some (Either.Left _) -> throwError NotASignalState
        | Some (Either.Right b) ->
            if b then aux c (Env.activate env w) else return false)
    | Watching (_, c, w) -> aux c (Env.activate env w)
    | Stop -> return false
    | _ -> return true
  in
  aux c Env.empty

let rec kill (c : command) (env : env) (h : heap) : command Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  match c with
  | Block (c, w) ->
      let* c' = kill c (Env.activate env w) h in
      return (Block (c', w))
  | Seq (c1, c2) ->
      let* c1' = kill c1 env h in
      return (Seq (c1', c2))
  | Par (c1, w1, c2, w2) ->
      let* c1' = kill c1 (Env.activate env w1) h
      and* c2' = kill c2 (Env.activate env w2) h in
      return (Par (c1', w1, c2', w2))
  | When (s, c, w) ->
      let* c' = kill c (Env.activate env w) h in
      return (When (s, c', w))
  | Watching (s, c, w) -> (
      let* a = getVariable env s in
      let* v = getLocation h a in
      match v with
      | Some (Either.Right b) ->
          if b then return Skip
          else
            let* c' = kill c (Env.activate env w) h in
            return (Watching (s, c', w))
      | _ -> throwError NotASignalState)
  | _ -> return c

(* AAT NESXT INSTANT *)
let run (m : Intermediate.statement method_defn list) c : unit Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  let rec aux c h =
    Logs.debug (fun m -> m "start of a microstep");
    let* kont, _, heapAfterReduce = reduce m c Env.empty h in
    match kont with
    | Ret -> throwError ReturnStatementInProcess
    | Continue -> return ()
    | Suspend suspendedCommand ->
        let* b = canProgress suspendedCommand heapAfterReduce in
        if b then aux suspendedCommand heapAfterReduce
        else
          let _ = Logs.debug (fun m -> m "new instant") in
          let* nextCommand = kill suspendedCommand Env.empty heapAfterReduce in
          let* b = canProgress nextCommand (reset heapAfterReduce) in
          if b then aux nextCommand (reset heapAfterReduce)
          else
            (* The machine should freeze, waiting for external events *)
            let _ = Logs.debug (fun m -> m "no further progress") in
            return ()
  in
  aux (Block (c, Env.emptyFrame)) Heap.empty

let start (m : Intermediate.statement method_defn list) (c : Intermediate.statement)
    : unit =
  match run m (Domain.initCommand c) with
  | Either.Left e ->
      Format.fprintf Format.std_formatter "ERROR : %a\n" pp_print_error e
  | Either.Right () -> ()
