open Common
open Saillib.MyUtil
open Saillib.Heap
open Saillib.Env
open Intermediate

let mapM (f : 'a -> 'b option) (s : 'a Store.t) : 'b Store.t option =
  let s' = Store.filter_map (fun _ x -> f x) s in
  if Store.cardinal s = Store.cardinal s' then Some s' else None

(* Semantics domain *)

type env = location Env.t 
  
type heap = (value, bool) sum H.t

(* let rec freshn (h : 'a H.t) n : H.address list * 'a H.t = 
  if n > 0 then 
    let (a, h') = H.fresh h in 
    let (l, h'') = freshn h' (n-1) in (a::l, h'')
  else ([], h)*)

let collect (h : heap) (l : H.address list) : H.address list option =
  let rec aux h l acc =  
  match l with 
    | [] -> Some acc
    | l::t -> 
        if List.mem l acc then aux h t acc 
        else 
          begin match H.fetch h l with 
          | Some (Some (Inl v)) -> 
            let x = locationsOfValue v in 
            aux h (x @ t) (l::acc)
          | Some (Some (Inr _)) -> aux h t (l::acc)
          | Some None -> aux h t (l::acc)
          | None -> None
          end 
        in aux h l []

  let drop (h : heap) (l : H.address list) : heap option = 
    collect h l >>= fold_leftM Heap.free h

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
  | Div, VInt x, VInt y -> Some (VInt (x / y))
  | Div, VFloat x, VFloat y -> Some (VFloat (x /. y))
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

let pp_location (pf : Format.formatter) (a,_) = 
  H.pp_address pf a 

let rec evalL (env : env) (h : heap) (e : expression) : location option =
    Logs.debug (fun m -> m "evaluate left value %a \n" pp_expression e);
  match e with
    | Var x -> 
      let* l = Env.fetchLoc env x in 
      Logs.debug (fun m -> m "fetchVar %s %a \n" x pp_location l);
      Env.fetchLoc env x
    | Deref e -> 
        let* v = evalR env h e in 
        begin match v with VLoc l -> Some l | _ -> None end
    | StructRead (e, f) ->
        let* (a, o) = evalL env h e in
        Some (a, o @ [ Field f ])
    | ArrayRead (e1, e2) -> (
        let* (a, o) = evalL env h e1 and* v = evalR env h e2 in
        match v with VInt n -> Some (a, o @ [ Indice n ]) | _ -> None)
    | _ -> None
and evalR (env : env) (h : heap) (e : expression) : value option =
    Logs.debug (fun m -> m "evaluate right value <<%a>> \n" pp_expression e);
  let rec aux e =
    match e with
    | Var x -> 
      Logs.debug (fun m -> m "fetch var  0\n");
        let* (a, o) = Env.fetchLoc env x in
        Logs.debug (fun m -> m "fetch value <<%a>> 0\n" H.pp_address a);
        let* v = H.fetch h a in 
        begin match v with 
            Some (Inr _) -> 
              Logs.debug (fun m -> m "evaluate right value <<%a>> 1 \n" pp_expression e); 
              None
          | Some (Inl v) -> 
            Logs.debug (fun m -> m "evaluate right value <<%a>> 2 \n" pp_expression e);
            readValue o v
          | None -> 
            Logs.debug (fun m -> m "evaluate right value <<%a>> 3\n" pp_expression e);
            None
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
          begin match H.fetch h a with 
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

let rec buildEnv (l : (value * sailtype) list) (h : heap) : (location list * heap) option =
  match l with 
      [] -> Some ([], h) 
    | (VLoc l, RefType _ )::m -> 
        let* (n,h') = buildEnv m h in Some (l::n,  h') 
     | (_, RefType _)::_ -> None
    | (v, _)::m -> 
        let (a, h') = H.fresh h  in
        let* h' = H.update h' (a, Inl v) in   
        let* (n, h'') = buildEnv m h' in 
        Some ((a,[])::n, h'')

let rec freshn (h : heap) n : H.address list * heap = 
  if n > 0 then let (a,h') = H.fresh h in let (l,h'') = freshn h' (n-1) in (a::l,h'')
  else ([], h)

let reduce (p : command method_defn list) (c : command) (env : env) (h : heap) :
    (result * frame * heap) option =
  let rec aux c env h  : (result * frame * heap) option = 
  Logs.debug (fun m -> m "execute command %a \n" pp_command c);
  match c with
  | DeclVar (_, x, _) ->
      let a, h0 = H.fresh h in
      Some (Continue, Env.singleton x (a,[]), h0)
  | DeclSignal s ->
      let a, h0 = H.fresh h in
      let* h1 = H.update h0 (a, Inr false) in
      Some (Continue, Env.singleton s (a,[]), h1)
  | Skip -> Some (Continue, Env.emptyFrame, h)
  | Assign (e1, e2) ->
      let* (a, o) = evalL env h e1 in 
      let*  v = evalR env h e2 in
      Logs.debug (fun m -> m "TESTING 0\n");
      let* u = H.fetch h a in
        begin match u with 
          None -> 
            Logs.debug (fun m -> m "TESTING 1\n");

            let* h' = H.update h (a, Inl v) in (* plutot faire un filtrage sur le chemin et mettre à jour direct si vide*)
            Some (Continue, Env.emptyFrame, h') (* dans ce cas update value prend un chemin non vide *)
          | Some u ->
            Logs.debug (fun m -> m "TESTING 2\n");

            let* v0 = inl u in
            let* v' = updateValue v0 o v in (* update value -> option value pour representer cas non initialisé *)
            let* h' = H.update h (a, Inl v') in
            Some (Continue, Env.emptyFrame, h')
          end
  | AssignBox (e1, e2) ->
      let* (a, o) = evalL env h e1 and* v = evalR env h e2 in
      let* u = H.fetch h a in 
      let (a', h') = H.fresh h in 
      let* h'' = H.update h' (a', Inl v) in
      begin match u with 
          None -> 
            let v' = (VLoc (a', [])) in 
            let* h''' = H.update h'' (a, Inl v') in
            Some (Continue, Env.emptyFrame, h''')
        | Some (Inl u) -> 
            let* v' = updateValue u o (VLoc (a', [])) in
            let* h''' = H.update h'' (a, Inl v') in      
            Some (Continue, Env.emptyFrame, h''')
        | Some _ -> None
      end
  | Seq (c1, c2) -> (
      match aux c1 env h with
      | None -> None
      | Some (Continue, w', h') -> 
        let* w = Env.top env in 
        aux c2 (Env.activate env (Env.merge w w')) h'
      | Some (Suspend c1', w, h') -> Some (Suspend (Seq (c1', c2)), w, h')
      | Some (Ret, w, h') -> Some (Ret, w, h'))
  | Block (c, w) -> (
      match aux c (Env.activate env w) h with
      | Some (Suspend c', w', h') -> Some (Suspend (Block (c', Env.merge w w')), Env.emptyFrame,h')
      | Some (r, w' ,h') ->
          let  l = Env.allValues (Env.merge w w') in
          let* cleanHeap = drop h' (List.map fst l) in (* be careful not to drop shared ref*)
          Some (r, Env.emptyFrame, cleanHeap)
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
    begin match filter v p with 
        Some s -> 
          let (l, h') = freshn h (List.length s) in 
          let vars = List.map fst s in 
          let vals = List.map (fun x -> Inl(snd x)) s in  
          let varmap = List.map (uncurry Env.singleton) (List.combine vars (List.map (fun x -> (x,[])) l)) in
          let w = List.fold_left Env.merge Env.emptyFrame varmap in 
          let locmap = List.combine l vals in 
          let* h'' = fold_leftM H.update h' locmap in
          aux (Block (c, w)) env h'' 
      | None -> aux (Case (e,pl)) env h
    end 
  | Invoke (x, el) -> 
      let* callee = List.find_opt (fun m-> m.m_name = x) p in
      let formal_params = List.map fst callee.m_params in
      let types = List.map snd callee.m_params in
      let* real_params = listMapM (evalR env h) el in
      let typed_params = List.combine real_params types in 
      let* (l,h') = buildEnv typed_params h in 
      let varmap = List.map (uncurry Env.singleton) (List.combine formal_params l) in
      let w = List.fold_left Env.merge Env.emptyFrame varmap in 
      let c = callee.m_body in 
      let* (r,w,h) = aux (Block(c,w)) Env.empty h' in 
      begin match r with Ret -> Some (Continue, w, h) | _ -> None end 
  | Return -> Some (Ret, Env.emptyFrame, h)
  | Emit (s) ->
      let* (a,_) = Env.fetchLoc env s in
      let* h' = Heap.update h (a, Inr true)
      in Some (Continue, Env.emptyFrame, h')
  | When (s, c, w) -> 
      let* (a,_) = Env.fetchLoc env s in (* _ is not pretty *)
      begin match H.fetch h a with 
        | Some (Some (Inr false)) -> Some (Suspend (When (s,c,w)), Env.emptyFrame, h)
        | Some (Some (Inr true)) -> 
          begin match aux c (Env.activate env w) h with 
            | Some (Suspend (c'), w', h') -> Some (Suspend (When(s, c',Env.merge w w')), Env.emptyFrame, h')
            | Some (k, w', h') -> 
              let  l = Env.allValues (Env.merge w w') in
              let* cleanHeap = drop h' (List.map fst l) in
              Some (k, Env.emptyFrame, cleanHeap)
            | None -> None
          end
        | _ -> None
      end    
  | Watching (s,c,w) -> 
    begin match aux c env h with 
        | Some (Suspend (c'), w', h') -> Some (Suspend (Watching(s, c',Env.merge w w')), Env.emptyFrame, h')
        | Some (k, w', h') -> 
          let  l = Env.allValues (Env.merge w w') in
          let* cleanHeap = drop h' (List.map fst l) in
          Some (k, Env.emptyFrame, cleanHeap)
        | None -> None
    end
  | Par (c1, w1, c2, w2) ->
    let* (k1, w1', h') = aux c1 (Env.activate env w1) h in 
    let* (k2, w2',  h'') = aux c2 (Env.activate env w2) h' in
    begin match (k1, k2) with
      | (Continue, Continue) -> 
        let  l = Env.allValues (Env.merge w1 (Env.merge w2 (Env.merge w1' w2'))) in
        let* cleanHeap = drop h' (List.map fst l) in
        Some (Continue, Env.emptyFrame, cleanHeap)
      | (Continue, Suspend(c)) -> Some (Suspend (Par (Skip, Env.merge w1 w1', c, Env.merge w2 w2')), Env.emptyFrame, h'')
      | (Suspend c, Continue) -> Some (Suspend (Par (c, Env.merge w1 w1', Skip, Env.merge w2 w2')), Env.emptyFrame, h'')
      | (Suspend c1', Suspend c2') -> 
          Some (Suspend (Par (c1', Env.merge w1 w1', c2', Env.merge w2 w2')), Env.emptyFrame, h'') 
      | _ -> None 
    end

  in aux c env h

  let rec collect (c : command) (env : env) : H.address list =
    match c with 
      Block(c, w) -> List.map fst (Env.allValues w) @ collect c (Env.activate env w)
    | Seq (c1, _) -> collect c1 env
    | Par (c1, w1, c2, w2) -> collect c1 (Env.activate env w1) @ (List.map fst (Env.allValues w1))
        @ collect c2 (Env.activate env w2) @ (List.map fst (Env.allValues w2))
    | When (_, c, w) -> collect c (Env.activate env w) @ (List.map fst (Env.allValues w))
    | Watching (_, c, w) -> collect c (Env.activate env w) @ (List.map fst (Env.allValues w))
     | _ -> []

  let rec kill (c : command) (env : env) (h : heap): (command * H.address list) option =
    match c with 
        Block (c, w) -> let* (c', l) = kill c (Env.activate env w) h in Some (Block (c', w), l)
       | Seq(c1, c2) -> let* (c1', l) = kill c1 env h in Some (Seq (c1', c2), l)
      | Par (c1, w1, c2, w2) -> 
          let* (c1', l1) = kill c1 (Env.activate env w1) h
          and* (c2', l2) = kill c2 (Env.activate env w2) h
          in Some (Par (c1', w1, c2', w1), l1@l2) 
      | When (s,c, w) -> let* (c',l) = kill c (Env.activate env w) h in Some (When (s, c',w), l)
      | Watching (s,c, w) -> 
          let* (a,_) = Env.fetchLoc env s in
          let* v = H.fetch h a in
          begin match v with 
              Some (Inr b) ->  
                if b then Some (Skip, collect (Watching (s,c, w)) env)
                else let* (c', l) = kill c (Env.activate env w) h in Some (When (s, c', w), l)
            | _ -> None 
          end
      | _ -> Some (c, [])

(* AAT NESXT INSTANT *)
let run m c : unit option =
  let rec aux c h = 
    let t = reduce m c Env.empty h in (* None *)
    match t with 
      None -> failwith "Error in run"
      | Some (r, _, h') ->
    match r with 
      | Ret -> 
       
        failwith "Return should not occur at the process level"
      | Continue -> 
        Some () 
      | Suspend c -> 
        let* (c', l) = kill c Env.empty h in 
        let* h'' = drop h' l in aux c' h''
  in aux (Block (c, Env.emptyFrame)) Heap.empty


