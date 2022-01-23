open Common
open Saillib.MyUtil
(* open Saillib.Heap *)
(* open Saillib.Env *)
open Intermediate

let mapM (f : 'a -> 'b option) (s : 'a Store.t) : 'b Store.t option =
  let s' = Store.filter_map (fun _ x -> f x) s in
  if Store.cardinal s = Store.cardinal s' then Some s' else None

(* Semantics domain *)

type env = SailEnv.t 

let collect (h : SailHeap.t) (l : SailAddress.t list) : SailAddress.t list option =
  let rec aux h l acc =  
  match l with 
    | [] -> Some acc
    | l::t -> 
        if List.mem l acc then aux h t acc 
        else 
          begin match SailHeap.fetch h l with 
          | Some (Some (Inl v)) -> 
            let x = locationsOfValue v in 
            aux h (x @ t) (l::acc)
          | Some (Some (Inr _)) -> aux h t (l::acc)
          | Some None -> aux h t (l::acc)
          | None -> None
          end 
        in aux h l []

  let drop (h : SailHeap.t) (l : SailAddress.t list) : SailHeap.t option = 
    collect h l >>= fold_leftM SailHeap.free h

(* Dynamic statements *)

type result = Continue : result | Ret | Suspend of Intermediate.command

let pp_result (pf : Format.formatter) (r : result) : unit =
  match r with 
      Ret -> Format.fprintf pf "ret"
    | Continue -> Format.fprintf pf "continue"
    | Suspend (c) -> (pp_command pf c)

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


let rec evalL (env : env) (h : SailHeap.t) (e : expression) : Location.t option =
    Logs.debug (fun m -> m "evaluate left value < %a >" pp_expression e);
  match e with
    | Var x -> 
      SailEnv.fetchLoc env x
    | Deref e -> 
        let* v = evalR env h e in 
        begin match v with VLoc l -> Some l | _ -> None end
    | StructRead (e, f) ->
        let* (a, o) = evalL env h e in
        Some (a, o @ [ Field f ])
    | ArrayRead (e1, e2) -> (
        let* (a, o) = evalL env h e1 and* v = evalR env h e2 in
        match v with VInt n -> Some (a, o @ [ Indice n ]) | _ -> None)
    | _ ->
      Logs.debug (fun m -> m "HERE");
      None
and evalR (env : env) (h : SailHeap.t) (e : expression) : value option =
  let rec aux e =
    Logs.debug (fun m -> m "evaluate right value < %a >" pp_expression e);
    match e with
    | Var x -> 
        let* (a, o) = SailEnv.fetchLoc env x in
        let* v = SailHeap.fetch h a in 
        begin match v with 
            Some (Inr _) -> None
          | Some (Inl v) -> readValue o v
          | None -> None
        end
    | Literal c -> Some (valueOfLiteral c)
    | UnOp (u, e) -> aux e >>= evalunop u
    | BinOp (b, e1, e2) ->
        let* x = aux e1 and* y = aux e2 in
        evalBinop b x y
    | ArrayAlloc es ->
        let* l = optionlist (List.map aux es) in
        Some (VArray l)
    | ArrayRead (e1, e2) -> (
        let* v = aux e1 and* n = aux e2 in
        match (v, n) with VArray a, VInt n -> List.nth_opt a n | _ -> None)
    | StructAlloc es -> mapM aux es >>= fun x -> Some (VStruct x)
    | StructRead (e, f) -> (
        aux e >>= fun x ->
        match x with VStruct m -> Store.find_opt f m | _ -> None)
    | EnumAlloc (c, es) ->
        let* vs = optionlist (List.map aux es) in
        Some (VEnum (c, vs))
    | Ref (_,e) -> (* Enforce that mutability is respected *)
        let* a = evalL env h e in
        Some (VLoc a)
    | Deref e -> (
        let* v = aux e in
        match v with
        | VLoc (a, o) -> 
          begin match SailHeap.fetch h a with 
              Some u -> u >>= inl >>= readValue o
            | None -> None 
          end
        | _ -> None)
  in
  aux e


let rec filter (v : value) (p : pattern) : (string * value) list option =
  match (v, p) with  
    | (_, PVar x) -> Some [(x,v)]
    | (VEnum (x, l), PCons (y, m)) when x = y ->
      (listMapM  (uncurry filter) (List.combine l m)) >>= 
      fun l -> Some (List.concat l)
    | _ -> None 

let rec buildEnv (l : (value * sailtype) list) (h : SailHeap.t) : (location list * SailHeap.t) option =
  match l with 
      [] -> Some ([], h) 
    | (VLoc l, RefType _ )::m -> 
        let* (n,h') = buildEnv m h in Some (l::n,  h') 
     | (_, RefType _)::_ -> None
    | (v, _)::m -> 
        let (a, h') = SailHeap.fresh h  in
        let* h' = SailHeap.update h' (a, Inl v) in   
        let* (n, h'') = buildEnv m h' in 
        Some ((a,[])::n, h'')

let rec freshn (h : SailHeap.t) n : SailAddress.t list * SailHeap.t = 
  if n > 0 then let (a,h') = SailHeap.fresh h in let (l,h'') = freshn h' (n-1) in (a::l,h'')
  else ([], h)

let reduce (p : command method_defn list) (c : command) (env : env) (h : SailHeap.t) :
    (result * frame * SailHeap.t) option =
  let rec aux c env h  : (result * frame * SailHeap.t) option = 
  Logs.debug (fun m -> m "evaluate command < %a> " pp_command_short c); 
  Logs.debug (fun m -> m "current environment: %a" SailEnv.pp_t env);
  Logs.debug (fun m -> m "current heap: %a" SailHeap.pp_t h);
  match c with
  | DeclVar (_, x, _) ->
      let a, h0 = SailHeap.fresh h in
      Some (Continue, SailEnv.singleton x (a,[]), h0)
  | DeclSignal s ->
      let a, h0 = SailHeap.fresh h in
      let* h1 = SailHeap.update h0 (a, Inr false) in
      Some (Continue, SailEnv.singleton s (a,[]), h1)
  | Skip -> Some (Continue, SailEnv.emptyFrame, h)
  | Assign (e1, e2) ->
      let* (a, o) = evalL env h e1 in 
      let*  v = evalR env h e2 in
      let* u = SailHeap.fetch h a in
        begin match u with 
          None -> 
            let* h' = SailHeap.update h (a, Inl v) in (* plutot faire un filtrage sur le chemin et mettre à jour direct si vide*)
            Some (Continue, SailEnv.emptyFrame, h') (* dans ce cas update value prend un chemin non vide *)
          | Some u ->
            let* v0 = inl u in
            let* v' = updateValue v0 o v in (* update value -> option value pour representer cas non initialisé *)
            let* h' = SailHeap.update h (a, Inl v') in
            Some (Continue, SailEnv.emptyFrame, h')
          end
  | AssignBox (e1, e2) ->
      let* (a, o) = evalL env h e1 and* v = evalR env h e2 in
      let* u = SailHeap.fetch h a in 
      let (a', h') = SailHeap.fresh h in 
      let* h'' = SailHeap.update h' (a', Inl v) in
      begin match u with 
          None -> 
            let v' = (VLoc (a', [])) in 
            let* h''' = SailHeap.update h'' (a, Inl v') in
            Some (Continue, SailEnv.emptyFrame, h''')
        | Some (Inl u) -> 
            let* v' = updateValue u o (VLoc (a', [])) in
            let* h''' = SailHeap.update h'' (a, Inl v') in      
            Some (Continue, SailEnv.emptyFrame, h''')
        | Some _ -> None
      end
  | Seq (c1, c2) -> (
      match aux c1 env h with
      | None -> None
      | Some (Continue, w', h') -> 
        let* env' = SailEnv.push env w' in 
        begin match aux c2 env' h' with
          None -> None  
          | Some (k, w, h'') -> Some (k, SailEnv.merge w' w, h'')
        end
      | Some (Suspend c1', w, h') -> Some (Suspend (Seq (c1', c2)), w, h')
      | Some (Ret, w, h') -> Some (Ret, w, h'))
  | Block (c, w) -> (
      match aux c (SailEnv.activate env w) h with
      | Some (Suspend c', w', h') -> Some (Suspend (Block (c', SailEnv.merge w w')), SailEnv.emptyFrame,h')
      | Some (r, w' ,h') ->
          let  l = SailEnv.allValues (SailEnv.merge w w') in
          let* cleanHeap = drop h' (List.map fst l) in (* be careful not to drop shared ref*)
          Some (r, SailEnv.emptyFrame, cleanHeap)
      | _ -> None)
  | If (e, c1, c2) -> (
      let* v = evalR env h e in
      match v with
      | VBool b -> if b then aux (Block (c1,SailEnv.emptyFrame)) env h else aux (Block (c2,SailEnv.emptyFrame)) env h
      | _ -> None)
  | While (e, c) -> (
      let* v = evalR env h e in
      match v with
      | VBool b -> 
        if b then 
          aux (Seq (Block (c,SailEnv.emptyFrame), While(e,c))) env h 
        else Some (Continue, SailEnv.emptyFrame, h)
      | _ -> None)
  | Case (_, []) -> None
  | Case (e,(p,c)::pl) -> 
    let* v = evalR env h e in 
    begin match filter v p with 
        Some s -> 
          let (l, h') = freshn h (List.length s) in 
          let vars = List.map fst s in 
          let vals = List.map (fun x -> Inl(snd x)) s in  
          let varmap = List.map (uncurry SailEnv.singleton) (List.combine vars (List.map (fun x -> (x,[])) l)) in
          let w = List.fold_left SailEnv.merge SailEnv.emptyFrame varmap in 
          let locmap = List.combine l vals in 
          let* h'' = fold_leftM SailHeap.update h' locmap in
          aux (Block (c, w)) env h'' 
      | None -> aux (Case (e,pl)) env h
    end 
  | Invoke (x, [e]) when x = "print_string" -> 
      begin match evalR env h e with 
        Some (VString str) -> print_string str; Some  (Continue, SailEnv.emptyFrame, h)
        | _ -> None
        end
  | Invoke (x, [e]) when x = "print_int" -> 
    begin match evalR env h e with 
      Some (VInt str) -> print_int str; Some  (Continue, SailEnv.emptyFrame, h)
      | _ -> None
      end
  | Invoke (x, []) when x = "print_newline" -> 
    print_newline (); Some  (Continue, SailEnv.emptyFrame, h) 
  | Invoke (x, [e1;e2]) when x = "box" -> 
      let* v = evalR env h e1 in 
      Logs.debug (fun m -> m "COCOCO"); 
      let* v' = evalR env h e2 in
      begin match v' with 
        VLoc (a,o) ->
          let (a', h') = SailHeap.fresh h in
          let* u = SailHeap.fetch h a in
          begin match u with 
          None -> 
            (* assert o = [] ?? *)
            (
              let* h'' = SailHeap.update h' (a, Inl (VLoc (a',[]))) in (* plutot faire un filtrage sur le chemin et mettre à jour direct si vide*)
              let* h''' = SailHeap.update h'' (a', Inl v) in
              Some (Continue, SailEnv.emptyFrame, h''')) 
            (* dans ce cas update value prend un chemin non vide *)
          | Some u ->
            Logs.debug (fun m -> m "COCOCO 2"); 
            let* v0 = inl u in
            let* v' = updateValue v0 o v in (* update value -> option value pour representer cas non initialisé *)
            let* h'' = SailHeap.update h' (a, Inl (VLoc (a',[]))) in
            let* h''' = SailHeap.update h'' (a', Inl v') in
            Some (Continue, SailEnv.emptyFrame, h''')
          end
        | _ -> None 
        end
  | Invoke (x, el) -> 
      let* callee = List.find_opt (fun m-> m.m_name = x) p in
      let formal_params = List.map fst callee.m_params in
      let types = List.map snd callee.m_params in
      let* real_params = listMapM (evalR env h) el in
      let typed_params = List.combine real_params types in 
      let* (l,h') = buildEnv typed_params h in 
      let varmap = List.map (uncurry SailEnv.singleton) (List.combine formal_params l) in
      let w = List.fold_left SailEnv.merge SailEnv.emptyFrame varmap in 
      let c = callee.m_body in 
      let* (r,w,h) = aux (Block(c,w)) SailEnv.empty h' in 
      begin match r with Ret -> Some (Continue, w, h) | _ -> None end 
  | Return -> Some (Ret, SailEnv.emptyFrame, h)
  | Emit (s) ->
      let* (a,_) = SailEnv.fetchLoc env s in
      let* h' = SailHeap.update h (a, Inr true)
      in Some (Continue, SailEnv.emptyFrame, h')
  | When (s, c, w) -> 
      let* (a,_) = SailEnv.fetchLoc env s in (* _ is not pretty *)
      begin match SailHeap.fetch h a with 
        | Some (Some (Inr false)) -> Some (Suspend (When (s,c,w)), SailEnv.emptyFrame, h)
        | Some (Some (Inr true)) -> 
          begin match aux c (SailEnv.activate env w) h with 
            | Some (Suspend (c'), w', h') -> Some (Suspend (When(s, c',SailEnv.merge w w')), SailEnv.emptyFrame, h')
            | Some (k, w', h') -> 
              let  l = SailEnv.allValues (SailEnv.merge w w') in
              let* cleanHeap = drop h' (List.map fst l) in
              Some (k, SailEnv.emptyFrame, cleanHeap)
            | None -> None
          end
        | _ -> None
      end    
  | Watching (s,c,w) -> 
    begin match aux c env h with 
        | Some (Suspend (c'), w', h') -> Some (Suspend (Watching(s, c',SailEnv.merge w w')), SailEnv.emptyFrame, h')
        | Some (k, w', h') -> 
          let  l = SailEnv.allValues (SailEnv.merge w w') in
          let* cleanHeap = drop h' (List.map fst l) in
          Some (k, SailEnv.emptyFrame, cleanHeap)
        | None -> None
    end
  | Par (c1, w1, c2, w2) ->
    let* (k1, w1', h') = aux c1 (SailEnv.activate env w1) h in 
    let* (k2, w2',  h'') = aux c2 (SailEnv.activate env w2) h' in
    begin match (k1, k2) with
      | (Continue, Continue) -> 
        let  l = SailEnv.allValues (SailEnv.merge w1 (SailEnv.merge w2 (SailEnv.merge w1' w2'))) in
        let* cleanHeap = drop h' (List.map fst l) in
        Some (Continue, SailEnv.emptyFrame, cleanHeap)
      | (Continue, Suspend(c)) -> Some (Suspend (Par (Skip, SailEnv.merge w1 w1', c, SailEnv.merge w2 w2')), SailEnv.emptyFrame, h'')
      | (Suspend c, Continue) -> Some (Suspend (Par (c, SailEnv.merge w1 w1', Skip, SailEnv.merge w2 w2')), SailEnv.emptyFrame, h'')
      | (Suspend c1', Suspend c2') -> 
          Some (Suspend (Par (c1', SailEnv.merge w1 w1', c2', SailEnv.merge w2 w2')), SailEnv.emptyFrame, h'') 
      | _ -> None 
    end

  in aux c env h

  let rec collect (c : command) (env : env) : SailAddress.t list =
    match c with 
      Block(c, w) -> List.map fst (SailEnv.allValues w) @ collect c (SailEnv.activate env w)
    | Seq (c1, _) -> collect c1 env
    | Par (c1, w1, c2, w2) -> collect c1 (SailEnv.activate env w1) @ (List.map fst (SailEnv.allValues w1))
        @ collect c2 (SailEnv.activate env w2) @ (List.map fst (SailEnv.allValues w2))
    | When (_, c, w) -> collect c (SailEnv.activate env w) @ (List.map fst (SailEnv.allValues w))
    | Watching (_, c, w) -> collect c (SailEnv.activate env w) @ (List.map fst (SailEnv.allValues w))
     | _ -> []

  let rec kill (c : command) (env : env) (h : SailHeap.t): (command * SailAddress.t list) option =
    match c with 
        Block (c, w) -> let* (c', l) = kill c (SailEnv.activate env w) h in Some (Block (c', w), l)
       | Seq(c1, c2) -> let* (c1', l) = kill c1 env h in Some (Seq (c1', c2), l)
      | Par (c1, w1, c2, w2) -> 
          let* (c1', l1) = kill c1 (SailEnv.activate env w1) h
          and* (c2', l2) = kill c2 (SailEnv.activate env w2) h
          in Some (Par (c1', w1, c2', w1), l1@l2) 
      | When (s,c, w) -> let* (c',l) = kill c (SailEnv.activate env w) h in Some (When (s, c',w), l)
      | Watching (s,c, w) -> 
          let* (a,_) = SailEnv.fetchLoc env s in
          let* v =SailHeap.fetch h a in
          begin match v with 
              Some (Inr b) ->  
                if b then Some (Skip, collect (Watching (s,c, w)) env)
                else let* (c', l) = kill c (SailEnv.activate env w) h in Some (When (s, c', w), l)
            | _ -> None 
          end
      | _ -> Some (c, [])

(* AAT NESXT INSTANT *)
let run m c : unit option =
  let rec aux c h = 
    let t = reduce m c SailEnv.empty h in (* None *)
    match t with 
        None -> 
          Format.printf "\nEvaluation error, please check logs\n"; None
      | Some (r, _, h') ->
          Logs.debug (fun m -> m "Enf of the instant : %a" SailHeap.pp_t h');
          match r with 
            | Ret ->        
              failwith "Return should not occur at the process level"
            | Continue -> Some () 
            | Suspend c -> 
              let* (c', l) = kill c SailEnv.empty h in 
              let* h'' = drop h' l in aux c' h''
  in aux (Block (c, SailEnv.emptyFrame)) SailHeap.empty


