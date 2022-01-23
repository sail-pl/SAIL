open Ast
open Intermediate
open Saillib.Env

let cpt = ref 0
let inc () = 
  let x = !cpt in 
  let _ = cpt := !cpt +1 in 
  x

let removeCalls (e : Ast.expression) : Intermediate.expression *  (string * string * Intermediate.expression list) list = 
  let rec aux e : Intermediate.expression *  (string * string * Intermediate.expression list) list = 
  match e with 
    | Ast.Variable x -> Intermediate.Var x, []
    | Ast.Literal c -> Intermediate.Literal c, [] 
    | Ast.UnOp(u, e) -> let (e, l) = aux e in Intermediate.UnOp(u, e), l
    | Ast.BinOp(n, e1, e2) -> let (e1,l1) = aux e1 in let (e2, l2) = aux e2 in Intermediate.BinOp(n,e1,e2),l1@l2
    | Ast.Ref(b,e) -> let (e,l) = aux e in Intermediate.Ref(b,e), l
    | Ast.Deref(e) -> let (e,l) = aux e in Intermediate.Deref(e), l
    | Ast.ArrayRead (e1, e2) -> 
      let (e1,l1) = aux e1 in 
      let (e2,l2) = aux e2 in
        Intermediate.ArrayRead (e1, e2), l1 @ l2
    | Ast.ArrayStatic (el) -> 
        let l = (List.map aux el) in
        let el = List.map fst l in
        let l2 = List.fold_left (fun x (_,y) -> x@y) [] l in 
        Intermediate.ArrayAlloc el, l2
    | Ast.StructRead (e,f) -> 
        let (e,l) = aux e in Intermediate.StructRead(e,f), l
    | Ast.StructAlloc (fel) -> 
        let m = List.map fst fel in
        let n = List.map snd fel in 
        let l = (List.map aux n) in
        let el = List.map fst l in
        let l2 = List.fold_left (fun x (_,y) -> x@y) [] l in
        let s = List.fold_left (fun x (y,e) -> Store.add y e x) Store.empty (List.combine m el) in
        Intermediate.StructAlloc(s), l2
    | Ast.EnumAlloc (x,el) ->
      let l = (List.map aux el) in
      let el = List.map fst l in
      let l2 = List.fold_left (fun x (_,y) -> x@y) [] l in 
        Intermediate.EnumAlloc(x, el), l2
    | Ast.MethodCall (x, el) ->
      let l = (List.map aux el) in
      let el = List.map fst l in
      let l2 = List.fold_left (fun x y -> x@y) [] (List.map snd l) in 
      let var = "_x"^(string_of_int (inc ())) in 
        (Intermediate.Var var), l2@[(var, x, el)]
    in aux e

let mkcall ((x,m,el) : string * string * Intermediate.expression list) =
  [
    Intermediate.DeclVar (true, x, Common.Int); (* mettre le bon type*)
    Intermediate.Invoke(m, el@[Intermediate.Ref (true, Intermediate.Var x)]) (* modifier les méthodes *)
  ]

let seq_oflist (l : Intermediate.command list) : Intermediate.command =
  match l with 
    [] -> Skip 
    | h::t -> List.fold_left (fun x y -> Intermediate.Seq (x,y)) h t

let resvar = "_res"

let rec translate  (t : Ast.statement) : Intermediate.command = 
  match t with 
      | Ast.DeclVar (b,x,t) -> Intermediate.DeclVar(b,x,t)
      | Ast.DeclSignal (s) -> Intermediate.DeclSignal(s)
      | Ast.Assign (e1, e2) ->
        let (e1, l1) = removeCalls e1 in 
        let (e2, l2) = removeCalls e2 in 
        let n = List.concat (List.map mkcall (l1 @ l2)) in
        seq_oflist (n@[Intermediate.Assign(e1,e2)])
      | Ast.Seq [] -> Intermediate.Skip
      | Ast.Seq (h::t) -> 
          let h = translate  h
          and t = List.map (translate) t in
          List.fold_left (fun x y -> Seq (x, y)) h t
      | Ast.If(e, t1, t2) -> 
          let t1 = translate t1 in
          let t2 = begin match t2 with None -> Intermediate.Skip | Some t2 -> translate t2 end in            
          let (e, l) = removeCalls e in 
          let m = List.concat (List.map mkcall l) in
          seq_oflist (m @ [Intermediate.If(e, t1, t2)])
      | Ast.While (e, t) -> 
          let t = translate t in 
          let (e, l) = removeCalls e in 
          let m = List.concat (List.map mkcall l) in
          seq_oflist (m @ [Intermediate.While(e, t)])
      | Ast.Case(e, pl) -> 
          let (e,l) = removeCalls e in 
          let m = List.concat (List.map mkcall l) in
            let pl = (List.map (fun (x,y) -> (x, translate  y)) pl) in
            seq_oflist (m @ [Intermediate.Case(e,pl)])
      | Ast.Invoke(Some x, m, el) -> 
        let l = List.map removeCalls el in 
        let l1 = List.map fst l in 
        let l2 = List.concat (List.map snd l) in 
        let n = List.concat (List.map mkcall l2) in
        seq_oflist (n @ [Intermediate.Invoke (m, l1@[Intermediate.Ref (true, Intermediate.Var x)])])
      | Ast.Invoke(None, m ,el ) -> 
        let l = List.map removeCalls el in 
        let l1 = List.map fst l in 
        let l2 = List.concat (List.map snd l) in 
        let n = List.concat (List.map mkcall l2) in
        seq_oflist (n @ [Intermediate.Invoke (m, l1)])
      | Return None -> Intermediate.Return 
      | Return (Some e) -> 
          let (e,l) = removeCalls e in
          let m = List.concat (List.map mkcall l) in 
          seq_oflist (m @ [Intermediate.Assign(Intermediate.Var resvar, e);Intermediate.Return])
      | Ast.Loop c -> 
        Intermediate.While (Literal (Common.LBool true), translate c)
      | Run _ -> failwith "processes not supported yet"
      | Ast.Emit(s) -> Intermediate.Emit(s)
      | When (s, c) -> Intermediate.When(s, translate c, Env.emptyFrame)
      | Watching (s, c) -> Intermediate.Watching(s, translate c, Env.emptyFrame)
      | Await (s) -> Intermediate.When(s, Skip,Env.emptyFrame) 
      | Par (c) -> 
          begin match List.map translate c with 
            []-> Intermediate.Skip
            |[c] -> c
            |c1::c2::t -> 
              List.fold_left (fun x y -> Intermediate.Par (x,Env.emptyFrame,y,Env.emptyFrame)) c1 (c2::t)
          end 

let method_translator (m : Ast.statement Common.method_defn) : Intermediate.command Common.method_defn =
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
    m_body = translate m.m_body
  }

let process_translator (p : Ast.statement Common.process_defn) : Intermediate.command Common.process_defn =
  {
  p_name  = p.p_name;
  p_generics = p.p_generics;
  p_interface = p.p_interface;
  p_body = translate p.p_body
}

let program_translate (p : Ast.statement Common.program) : Intermediate.command Common.program = 
  {
    structs = p.structs;
    enums = p.enums;
    methods = List.map method_translator p.methods;
    processes = List.map process_translator p.processes
  }