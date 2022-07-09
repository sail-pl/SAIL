open SailParser
open Common
open Pass
open TypesCommon
open Monad
open Monoid
open Error


type expression = loc AstHir.expression
type statement = expression AstHir.statement

module MonoidSeq: Monoid with type t = expression AstHir.statement = struct
  type t = expression AstHir.statement
  let mempty = AstHir.Skip dummy_pos
  let mconcat = fun x y -> AstHir.Seq (dummy_pos, x,y) 
end 

module C = MonadCounter.M
module W = MonadWriter.Make (MonoidSeq)
module E = MonadError
module EC = MonadCounter.T(E)
module ECW = MonadWriter.MakeTransformer(EC)(MonoidSeq)


let freshVar n = "_x"^ (string_of_int n)

 module Pass : Body with
              type in_body = AstParser.statement and   
              type out_body = expression AstHir.statement  =  
struct
  type in_body = AstParser.statement
  type out_body = expression AstHir.statement
      

  let lower_expression (env : TypeEnv.t) (e : AstParser.expression) : expression ECW.t = 
    let open MonadSyntax(ECW) in
    let open MonadFunctions(ECW) in 

    let rec aux (e : AstParser.expression) : expression ECW.t  = 
    match e with 
      | loc, AstParser.Variable id  -> return (AstHir.Variable(loc, id))
      | loc, AstParser.Deref e -> 
        let+ e = aux e in AstHir.Deref (loc, e)
      | loc, AstParser.StructRead (e, id) ->
        let+ e = aux e in AstHir.StructRead (loc, e, id)
      | loc, AstParser.ArrayRead (e1, e2) ->
        let* e1 = aux e1 in 
        let+ e2 = aux e2 in 
        AstHir.ArrayRead(loc,e1,e2)
      | loc , AstParser.Literal l -> return (AstHir.Literal (loc, l))
      | loc, AstParser.UnOp (op, e) -> 
        let+ e = aux e in AstHir.UnOp (loc, op, e)
      | loc, AstParser.BinOp(op,e1,e2)->
        let* e1 = aux e1 in 
        let+ e2 = aux e2 in
        AstHir.BinOp (loc, op, e1, e2)
      | loc, AstParser.Ref (b, e) ->
        let+ e = aux e in AstHir.Ref(loc, b, e)
      | loc, AstParser.ArrayStatic el -> 
        let+ el = listMapM aux el in AstHir.ArrayStatic (loc, el)
      | loc, AstParser.StructAlloc (id, m) ->
        let+ m = mapMapM aux m in AstHir.StructAlloc (loc, id, m)
      | loc, AstParser.EnumAlloc (id, el) ->
        let+ el = listMapM aux el in  AstHir.EnumAlloc (loc, id, el)
      | loc, MethodCall (id, el) ->
        let open MonadOperator(E) in 
        try 
          let _proto_loc,proto = FieldMap.find id ((snd env).methods) in
          match proto.ret with 
            | None ->  Result.error [loc,"error methods in expressions should return a value"] |> EC.lift
            | Some rtype -> fun n ->
              let x = freshVar n in
              listMapM aux el n >>| fun ((el,_),n') -> 
              let open MonadSyntax(W) in 
               (
                let* () = AstHir.DeclVar (dummy_pos, true, x, Some rtype, None) |> W.write in
                let+ () = AstHir.Invoke(loc, Some x, id, el) |> W.write in
                AstHir.Variable (dummy_pos, x)
                ),n'
              

      with Not_found -> Result.error [loc, "call to undefined method"] |> EC.lift
      in aux e

  let buildSeq s1 s2 = AstHir.Seq (dummy_pos, s1, s2)

  let lower (c:in_body declaration_type) (env:TypeEnv.t) : out_body E.t = 
    let open MonadSyntax(EC) in
    let open MonadFunctions(ECW) in 
    let open MonadOperator(E) in 

  let rec aux  : in_body -> out_body EC.t   = function
    | l, AstParser.DeclVar (mut, id, t, e ) -> 
      begin match e with 
        | Some e -> let+ (e, s) = lower_expression env e in 
          buildSeq s (AstHir.DeclVar (l, mut,id, t, Some e))
        | None -> AstHir.DeclVar (l, mut,id, t, None) |> EC.pure
      end 

    | l, AstParser.DeclSignal s -> AstHir.DeclSignal (l,s) |> EC.pure
    | l, AstParser.Skip -> AstHir.Skip(l) |> EC.pure
    | l, AstParser.Assign(e1, e2) ->  
        let* e1,s1 = lower_expression env e1 in
        let+ e2,s2 = lower_expression env e2 in
        AstHir.Seq (dummy_pos, s1, AstHir.Seq (dummy_pos, s2, AstHir.Assign(l, e1, e2)))
    

    | l, AstParser.Seq(c1, c2) -> let+ c1 = aux c1 and* c2 = aux c2 in AstHir.Seq(l, c1, c2) 
    | l, AstParser.Par(c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in AstHir.Par(l, c1,c2)
    | l, AstParser.If(e, c1, Some c2) -> 
      let+ e,s = lower_expression env e and* c1 = aux c1 and* c2 = aux c2 in 
      AstHir.Seq (dummy_pos, s, AstHir.If(l, e, c1, Some (c2)))

    | l, AstParser.If( e, c1, None) -> 
        let+ (e, s) = lower_expression env e and* c1 = aux c1 in 
        AstHir.Seq (dummy_pos, s, AstHir.If(l, e, c1, None))
        
    | l, AstParser.While(e, c) -> 
      let+ (e, s) = lower_expression env e and* c = aux c in
      buildSeq s (AstHir.While(l, e,c))

 (*   | AstParser.Case(loc, e, cases) -> AstHir.Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | l, AstParser.Case(e, _cases) ->  let+ e,s = lower_expression env e in
        buildSeq s (AstHir.Case (l, e, []))

    | l, AstParser.Invoke(id, el) -> (fun n  -> 
        listMapM (lower_expression env) el n >>| fun ((el,s),n') -> 
        buildSeq s (AstHir.Invoke(l, Some (freshVar n'), id, el)),n'+1) 
      
    | l, AstParser.Return e -> 
        begin match e with 
        | None -> AstHir.Return(l, None) |> EC.pure 
        | Some e -> let+ e,s = lower_expression env e in
          buildSeq s (AstHir.Return(l, Some e))
      end

    | l, AstParser.Run(id, el) -> let+ el,s = listMapM (lower_expression env) el in buildSeq s (AstHir.Run(l, id, el))
    | l, AstParser.Loop c -> let+ c = aux c in AstHir.While(l, AstHir.Literal(dummy_pos, LBool true) , c) 
    | l, AstParser.Emit s -> AstHir.Emit(l,s) |> EC.pure
    | l, AstParser.Await s -> AstHir.When(l, s, AstHir.Skip(dummy_pos)) |> EC.pure
    | l, AstParser.When (s, c) -> let+ c = aux c in AstHir.When(l, s, c)
    | l, AstParser.Watching(s, c) ->  let+ c = aux c in AstHir.Watching(l, s, c)
    | l, AstParser.Block c -> let+ c = aux c in AstHir.Block(l, c) 

    in aux (c.body) 0 >>| fun (b,_) -> b
end