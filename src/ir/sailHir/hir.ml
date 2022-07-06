open SailParser
open Common
open Pass
open TypesCommon
open Monad
open Monoid
open Writer
open Error


type expression = loc AstHir.expression


module MonoidSeq: Monoid with type t = expression AstHir.statement = struct
  type t = expression AstHir.statement
  let mempty = AstHir.Skip dummy_pos
  let mconcat = fun x y -> AstHir.Seq (dummy_pos, x,y) 
end 

module P = Writer.Make (MonoidSeq)

module EP = MonadErrorTransformer(P)

module E = MonadError



 module Pass : Body with
              type in_body = AstParser.statement and   
              type out_body = expression AstHir.statement  =  
struct
  type in_body = AstParser.statement
  type out_body = expression AstHir.statement

  let cpt = ref 0
    let freshVar () = 
    let x = !cpt in 
    let _ = cpt := !cpt +1 in 
      "_x"^(string_of_int x)

  let lower_expression (env : sailtype FieldMap.t list * DeclEnv.t) (e : AstParser.expression) : expression EP.t = 
    let open MonadSyntax(EP) in
    let open MonadFunctions(EP) in 
    let rec aux (e : AstParser.expression) : expression EP.t  = 
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
        try 
          match (FieldMap.find id ((snd env).methods)).ret with 
            | None -> Result.error [loc,"error methods in expressions should return a value"] |> P.pure
            | Some rtype ->
              let x = freshVar () in
              let* el = listMapM aux el in
              let* () = P.write (AstHir.DeclVar (loc, true, x, Some rtype, None)) |> EP.lift  in
              let+ () = P.write (AstHir.Invoke(loc, Some x, id, el)) |> EP.lift  in 
              AstHir.Variable (loc, x)
      with Not_found -> Result.error [loc, "call to undefined method"] |> P.pure
      in aux e

  let buildSeq s1 s2 = AstHir.Seq (dummy_pos, s1, s2)

  let lower (c:in_body declaration_type) (env:TypeEnv.t) : out_body E.t = 
    let open MonadSyntax(E) in
    let open MonadFunctions(EP) in 
  let rec aux = function
    | l, AstParser.DeclVar (mut, id, t, e ) -> 
      begin match e with 
      | Some e -> let (e, s) = lower_expression env e in 
        let+ e in buildSeq s (AstHir.DeclVar (l, mut,id, t, Some e))
      | None -> AstHir.DeclVar (l, mut,id, t, None) |> E.lift
    end
    | l, AstParser.DeclSignal s -> AstHir.DeclSignal (l,s) |> E.lift
    | l, AstParser.Skip -> AstHir.Skip(l) |> E.lift
    | l, AstParser.Assign(e1, e2) -> 
      let (e1, s1) = lower_expression env e1 and (e2, s2) = lower_expression env e2 in
      let+ e1 and* e2 in
      AstHir.Seq (dummy_pos, s1, AstHir.Seq (dummy_pos, s2, AstHir.Assign(l, e1, e2)))


    | l, AstParser.Seq(c1, c2) -> let+ c1 = aux c1 and* c2 = aux c2 in AstHir.Seq(l, c1, c2) 
    | l, AstParser.Par(c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in AstHir.Par(l, c1,c2)
    | l, AstParser.If(e, c1, Some c2) -> 
      let (e, s) = lower_expression env e in 
      let+ e and*  c1 = aux c1 and* c2 = aux c2 in 
      AstHir.Seq (dummy_pos, s, AstHir.If(l, e, c1, Some (c2)))

    | l, AstParser.If( e, c1, None) -> 
        let (e, s) = lower_expression  env e in 
        let+ e and* c1 = aux c1 in 
        AstHir.Seq (dummy_pos, s, AstHir.If(l, e, c1, None))
    | l, AstParser.While(e, c) -> 
      let (e,s) = lower_expression env e in
      let+ c = aux c and* e in buildSeq s (AstHir.While(l, e,c))
 (*   | AstParser.Case(loc, e, cases) -> AstHir.Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | l, AstParser.Case(e, _cases) -> 
      let (e,s) = lower_expression env e in 
      let+ e in buildSeq s (AstHir.Case (l, e, []))
    | l, AstParser.Invoke(id, el) -> 
      let (el, s) = listMapM (lower_expression env) el in 
      let+ el in buildSeq s (AstHir.Invoke(l, Some (freshVar ()), id, el))
    | l, AstParser.Return e -> 
        begin match e with 
        | None -> AstHir.Return(l, None) |> E.lift 
        | Some e -> let (e,s) = lower_expression env e in let+e in buildSeq s (AstHir.Return(l, Some e))
      end
    | l, AstParser.Run(id, el) -> 
      let (el, s) = listMapM (lower_expression env) el in let+ el in buildSeq s (AstHir.Run(l, id, el))
    | l, AstParser.Loop c -> let+ c = aux c in  AstHir.While(l, AstHir.Literal(dummy_pos, LBool true) , c) 
    | l, AstParser.Emit s -> AstHir.Emit(l,s) |> E.lift
    | l, AstParser.Await s -> AstHir.When(l, s, AstHir.Skip(dummy_pos)) |> E.lift
    | l, AstParser.When (s, c) -> let+ c = aux c in AstHir.When(l, s, c)
    | l, AstParser.Watching(s, c) ->  let+ c = aux c in AstHir.Watching(l, s, c)
    | l, AstParser.Block c -> let+ c = aux c in AstHir.Block(l, c) 
  in aux c.body
end