open SailParser
open Common
open TypesCommon
open Monad
open AstHir

type expression = loc AstHir.expression
type statement = (loc,expression) AstHir.statement

open HirMonad.Make( struct
  type t = statement
  let mempty = {info=dummy_pos; stmt=Skip}
  let mconcat = fun x y -> {info=dummy_pos; stmt=Seq (x,y)}
  end)

module Pass = Pass.MakeFunctionPass (V)(
struct
  let name = "HIR"

  type in_body = AstParser.statement
  type out_body = statement
      

  let get_hint id env = 
    match List.nth_opt (HIREnv.get_closest env id) 0 with
    | None ->  ""
    | Some id ->  Printf.sprintf "Did you mean %s ?" id

  let lower_expression (e : AstParser.expression) : expression ECSW.t = 
    let open MonadSyntax(ECSW) in
    let open MonadFunctions(ECSW) in 

    let rec aux (info,e : AstParser.expression) : expression ECSW.t  = 
    match e with 
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
      | MethodCall ((l_id,id), el) ->
          let* m = ECSW.get_method id in 
          match m with
          | Some (_proto_loc,proto) -> 
            begin
            match proto.ret with 
            | Some rtype -> 
              let* n = ECSW.fresh in 
              let x = "__f" ^ string_of_int n in
              let* el = listMapM aux el in
              let* () =  {info; stmt=DeclVar (false, x, Some rtype, None)} |> ECSW.write in
              let+ () = {info; stmt=Invoke(Some x, (l_id,id), el)} |> ECSW.write in
              {info;exp=Variable x}
                
            | None -> ECSW.throw (Error.make info "methods in expressions should return a value")
            end
          | _ -> let* env = ECSW.get_env in let hint = get_hint id env in ECSW.throw (Error.make l_id "unknown method" ~hint)
      in aux e

  let lower_function (c:in_body Pass.function_type) (env:HIREnv.t) : out_body E.t = 
    let open MonadSyntax(ECS) in
    let open MonadFunctions(ECSW) in 
    let open MonadOperator(ECS) in 
    
  let rec aux (info,s : in_body) : out_body ECS.t = 
  
    let buildSeq s1 s2 = {info; stmt = Seq (s1, s2)} in 
    let buildStmt stmt = {info;stmt} in
    let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

    match s with
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

    | Loop c -> let+ c = aux c in 
      let e = {info; exp=Literal(LBool true)} in
      {info;stmt=While (e , c)}

    | Break () -> return {info; stmt=Break}
 (*   | Case(loc, e, cases) -> Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | Case (e, _cases) ->  let+ e,s = lower_expression e in
        buildSeqStmt s (Case (e, []))

    | Invoke ((l_id,id) as lid, el) ->
        let* m = ECS.get_method id and* env = ECS.get in
        let* () = ECS.log_if (Option.is_none m) (let hint = get_hint id env in (Error.make l_id "unknown method" ~hint))
        in
        let+ el,s = listMapM lower_expression el in
        buildSeqStmt s (Invoke(None, lid,el))

    | Return e -> 
        begin match e with 
        | None -> return @@ buildStmt (Return None)
        | Some e -> let+ e,s = lower_expression e in
          buildSeqStmt s (Return (Some e))
        end
    | Block c -> let+ c = aux c in buildStmt (Block c)
    
    | Run (l_id,id as lid, el) -> 
      let* () = ECS.log_if (id = c.name) (Error.make l_id "a process cannot call itself (yet)") in 
      let* m = ECS.get_process id and* env = ECS.get in
      let* () = ECS.log_if (Option.is_none m) (let hint = get_hint id env in (Error.make l_id "unknown process" ~hint)) in
      let* () =  ECS.log_if (c.bt = BMethod) (Error.make l_id "this is a process but methods cannot call processes") in
      let+ el,s = listMapM lower_expression el in 
      buildSeqStmt s (Run(lid, el))

    | _ when c.bt = Pass.BMethod -> 
      let+ () = ECS.log (Error.make info @@ Printf.sprintf "method %s : methods can't contain reactive statements" c.name) 
      in buildStmt Skip 

    | DeclSignal s -> return @@ buildStmt (DeclSignal s)
    | Emit s -> return @@ buildStmt (Emit s)
    | Await s -> return @@ buildStmt @@ When (s, buildStmt Skip)
    | When (s, c) -> let+ c = aux c in buildStmt (When (s, c))
    | Watching (s, c) ->  let+ c = aux c in buildStmt (Watching (s, c))
    | Par (c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in buildStmt (Par(c1,c2))

    in
    ECS.run (aux c.body env) |> E.recover {info=dummy_pos;stmt=Skip}
  end
 )