open Common
open TypesCommon
open Monad
open IrThir
open IrHir
open SailParser

module V = (
  struct 
    type t = bool * sailtype
    let string_of_var (_,t) = string_of_sailtype (Some t)
    let to_var _ (m:bool) (t:sailtype) = m,t
  end
)
module THIREnv = SailModule.SailEnv(V)
module E = Error.Logger
module EC = MonadState.CounterTransformer(E)
module ECS = struct
  include MonadState.T(EC)(THIREnv)

  let fresh = EC.fresh |> lift
  let throw e = E.throw e |> EC.lift |> lift
  let log e = E.log e |> EC.lift |> lift
  let log_if b e = E.log_if b e |> EC.lift |> lift
  let throw_if b e = E.throw_if b e |> EC.lift |> lift
  let run e = let e = EC.run e in E.bind e (fun (e,(_,s)) ->  E.pure (e,s))

  let get_decl id ty = bind get (fun e -> THIREnv.get_decl id ty e |> pure) 
end

module ECSW = struct
  include MonadWriter.MakeTransformer(ECS)( struct
  type t = Thir.statement
  let mempty : t = {info=dummy_pos; stmt=Skip}
  let mconcat : t -> t -> t = fun x y -> {info=dummy_pos; stmt=Seq (x,y)}
  end)

  let fresh = ECS.fresh |> lift
  let throw e = ECS.throw e |> lift 
  let log e = ECS.log e |> lift 
  let get_env = ECS.get |> lift

  let get_decl id ty = ECS.bind ECS.get (fun e -> THIREnv.get_decl id ty e |> ECS.pure) |> lift
end

let get_hint id env = Option.bind (List.nth_opt (THIREnv.get_closest id env) 0) (fun id -> Some (None,Printf.sprintf "Did you mean %s ?" id))



module Pass =  Pass.MakeFunctionPass(V)
(
  struct 
    let name = "Extract method call out of expressions (fixme : should be in hir but requires type inference)"

    type m_in = ThirUtils.statement
    type m_out = m_in

    type p_in = (HirUtils.statement,HirUtils.expression) AstParser.process_body
    type p_out = p_in

    open MonadFunctions(ECSW)    
    open MakeOrderedFunctions(String)
    open AstHir
    open Thir

    let lower_expression e : expression ECSW.t = 
      let open MonadSyntax(ECSW) in
      let open MonadOperator(ECSW) in
      let rec aux (e:expression)  = 
      let loc,_ as info = e.info in 
      match e.exp with 
        | Variable id -> return {info; exp=Variable id}
        | Deref e -> 
          let+ e = aux e in {info;exp=Deref e}
        | StructRead (o,e, id) ->
          let+ e = aux e in {info; exp=StructRead (o,e, id)}
        | ArrayRead (e1, e2) ->
          let* e1 = aux e1 in 
          let+ e2 = aux e2 in 
          {info; exp=ArrayRead(e1,e2)}
        | Literal l -> return {info; exp=Literal l}
        | UnOp (op, e) -> 
          let+ e = aux e in {info;exp=UnOp (op, e)}
        | BinOp(op,e1,e2)->
          let* e1 = aux e1 in 
          let+ e2 = aux e2 in
          {info; exp=BinOp (op, e1, e2)}
        | Ref (b, e) ->
          let+ e = aux e in {info;exp=Ref(b, e)}
        | ArrayStatic el -> 
          let+ el = ListM.map aux el in {info;exp=ArrayStatic el}
        | StructAlloc (o,id, m) ->
          let+ m = ListM.map (pairMap2 aux) m in {info; exp=StructAlloc (o,id, m)}
        | EnumAlloc (id, el) ->
          let+ el = ListM.map aux el in  {info;exp=EnumAlloc (id, el)}
        | MethodCall ((l_id,id), ((_,mname) as origin), el) -> (* THIS IS THE PROBLEM : WE NEED TO KNOW THE RETURN TYPE !! *)
          let* m = ECSW.get_decl id (Specific (mname,Method)) in 
          match m with
          | Some (_proto_loc,proto) -> 
            begin
            match proto.ret with 
            | Some rtype -> 
              let* n = ECSW.fresh in 
              let x = "__f" ^ string_of_int n in
              let* el = ListM.map aux el in
              let* () = ECSW.write {info=loc; stmt=DeclVar (false, x, Some rtype, None)} in
              let+ () = ECSW.write {info=loc; stmt=Invoke(Some x,origin, (l_id,id), el)} in
              {info;exp=Variable x}
                
            | None -> ECSW.throw (Error.make loc "methods in expressions should return a value (problem with THIR)")
            end
          | _ -> let* env = ECSW.get_env in let hint = get_hint id env in ECSW.throw (Error.make l_id "unknown method" ~hint)
        in aux e
  

    let lower_method (body,_proto : m_in * method_sig ) env _ : (m_out * THIREnv.D.t) E.t =
      let open MonadSyntax(ECS) in
      let open MonadOperator(ECS) in 
      let rec aux (s : statement) : statement ECS.t = 
        
        let buildSeq s1 s2 = {info=dummy_pos; stmt = Seq (s1, s2)} in 
        let buildStmt stmt = {info=dummy_pos;stmt} in
        let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in
        
        let info = s.info in 
        match s.stmt with
        | DeclVar (mut, id, t, e ) -> 
          begin match e with
            | Some e -> let+ (e, s) = lower_expression e in
              buildSeqStmt s (DeclVar (mut,id, t, Some e))
            | None -> return {info;stmt=DeclVar (mut,id, t, None)}
          end 
        | Skip -> return {info;stmt=Skip}
        | Assign(e1, e2) ->  
            let* e1,s1 = lower_expression e1 in
            let+ e2,s2 = lower_expression e2 in
            buildSeq s1 @@ buildSeqStmt s2 (Assign (e1, e2))
    
        | Seq (c1, c2) -> let+ c1 = aux c1 and* c2 = aux c2 in {info;stmt=Seq (c1, c2)}
        | If (e, c1, Some c2) -> 
          let+ e,s = lower_expression e and* c1 = aux c1 and* c2 = aux c2 in 
          buildSeqStmt s (If (e, c1, Some c2))
    
        | If ( e, c1, None) -> 
            let+ (e, s) = lower_expression e and* c1 = aux c1 in 
            buildSeqStmt s (If (e, c1, None))
            
        | Loop c -> 
          let+ c = aux c in
          buildStmt (Loop c)
    
        | Break -> return {info; stmt=Break}
        | Case (e, _cases) ->  let+ e,s = lower_expression e in
            buildSeqStmt s (Case (e, []))
    
        | Invoke (target, origin, lid, el) ->
            let+ el,s = ListM.map lower_expression el in
            buildSeqStmt s (Invoke(target, origin, lid,el))
    
        | Return e -> 
            begin match e with 
            | None -> return @@ buildStmt (Return None)
            | Some e -> let+ e,s = lower_expression e in
              buildSeqStmt s (Return (Some e))
            end
        | Block c -> let+ c = aux c in buildStmt (Block c)
    
        in
        ECS.run (aux body env) |> E.recover ({info=dummy_pos;stmt=Skip},snd env)

    let preprocess = Error.Logger.pure

    let lower_process (c:p_in process_defn) env _ = E.pure (c.p_body,snd env)

  end
)



