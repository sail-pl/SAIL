open Common
open TypesCommon
open Monad
open IrHir
open IrThir
open Pass

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
  let run e = let e = EC.run e in E.bind e (fun e -> fst e |> E.pure)

  let get_decl id ty = bind get (fun e -> THIREnv.get_decl e id ty |> pure) 
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

  let get_decl id ty = ECS.bind ECS.get (fun e -> THIREnv.get_decl e id ty |> ECS.pure) |> lift
end

let get_hint id env = 
  MonadOption.M.bind (List.nth_opt (THIREnv.get_closest env id) 0) (fun id -> Some (None,Printf.sprintf "Did you mean %s ?" id))



module Pass =  Pass.MakeFunctionPass(V)
(
  struct 
    let name = "Extract method call out of expressions"

    type in_body = IrThir.Thir.Pass.out_body
    type out_body = in_body

    open MonadFunctions(ECSW)    
    open MakeOrderedFunctions(String)
    open AstHir
    open Thir

    let lower_expression e : expression ECSW.t = 
      let open MonadSyntax(ECSW) in
      let rec aux (e:expression)  = 
      let loc,_ as info = e.info in 
      match e.exp with 
        | Variable id -> return {info; exp=Variable id}
        | Deref e -> 
          let+ e = aux e in {info;exp=Deref e}
        | StructRead (e, id) ->
          let+ e = aux e in {info; exp=StructRead (e, id)}
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
          let+ el = listMapM aux el in {info;exp=ArrayStatic el}
        | StructAlloc (id, m) ->
          let+ m = mapMapM aux m in {info; exp=StructAlloc (id, m)}
        | EnumAlloc (id, el) ->
          let+ el = listMapM aux el in  {info;exp=EnumAlloc (id, el)}
        | MethodCall ((l_id,id), mod_loc, el) ->
          let* m = ECSW.get_decl id (Specific (mod_loc.mname,Method)) in 
          match m with
          | Some (_proto_loc,_,proto) -> 
            begin
            match proto.ret with 
            | Some rtype -> 
              let* n = ECSW.fresh in 
              let x = "__f" ^ string_of_int n in
              let* el = listMapM aux el in
              let* () =  {info=loc; stmt=DeclVar (false, x, Some rtype, None)} |> ECSW.write in
              let+ () = {info=loc; stmt=Invoke(Some x,mod_loc, (l_id,id), el)} |> ECSW.write in
              {info;exp=Variable x}
                
            | None -> ECSW.throw (Error.make loc "methods in expressions should return a value")
            end
          | _ -> let* env = ECSW.get_env in let hint = get_hint id env in ECSW.throw (Error.make l_id "unknown method" ~hint)
        in aux e
  

    let lower_function (f : in_body function_type) env _ : out_body E.t =
      let open MonadSyntax(ECS) in
      let open MonadOperator(ECS) in 

      let rec aux (s : statement) : out_body ECS.t = 
        
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
            
        | While (e, c) -> 
          let+ e,s = lower_expression e and* c = aux c in
          buildSeqStmt s (While (e,c))
    
        | Break -> return {info; stmt=Break}
        | Case (e, _cases) ->  let+ e,s = lower_expression e in
            buildSeqStmt s (Case (e, []))
    
        | Invoke (target, origin, lid, el) ->
            let+ el,s = listMapM lower_expression el in
            buildSeqStmt s (Invoke(target, origin, lid,el))
    
        | Return e -> 
            begin match e with 
            | None -> return @@ buildStmt (Return None)
            | Some e -> let+ e,s = lower_expression e in
              buildSeqStmt s (Return (Some e))
            end
        | Block c -> let+ c = aux c in buildStmt (Block c)
        
        | Run (lid, el) -> 
          let+ el,s = listMapM lower_expression el in 
          buildSeqStmt s (Run(lid, el))
        | DeclSignal s -> return @@ buildStmt (DeclSignal s)
        | Emit s -> return @@ buildStmt (Emit s)
        | Await s -> return @@ buildStmt @@ When (s, buildStmt Skip)
        | When (s, c) -> let+ c = aux c in buildStmt (When (s, c))
        | Watching (s, c) ->  let+ c = aux c in buildStmt (Watching (s, c))
        | Par (c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in buildStmt (Par(c1,c2))
    
        in
        ECS.run (aux f.body env) |> E.recover {info=dummy_pos;stmt=Skip}
  end
)



