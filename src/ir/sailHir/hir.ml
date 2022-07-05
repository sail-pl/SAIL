open SailParser
open Common
open Pass
open TypesCommon
open Monad
open Monoid
open Writer


type expression = loc AstHir.expression


module MonoidSeq: Monoid with type t = expression AstHir.statement = struct
  type t = expression AstHir.statement
  let mempty = AstHir.Skip dummy_pos
  let mconcat = fun x y -> AstHir.Seq (dummy_pos, x,y) 
end 

module P = Writer.Make (MonoidSeq)


 module Pass (*: Body with
              type in_body = AstParser.statement and   
              type out_body = expression AstHir.statement *) =  
struct
  type in_body = AstParser.statement
  type out_body = expression AstHir.statement

  let cpt = ref 0
    let freshVar () = 
    let x = !cpt in 
    let _ = cpt := !cpt +1 in 
      "_x"^(string_of_int x)

  let lower_expression (env : sailtype FieldMap.t list * DeclEnv.t) (e : AstParser.expression) : expression P.t = 
    let open P in
    let open MonadSyntax(P) in
    let open MonadFunctions(P) in 
    let rec aux (e : AstParser.expression) : expression P.t  = 
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
            | None -> failwith "error methods in expressions should return a value"
            | Some rtype ->
              let x = freshVar () in
              let* el = listMapM aux el in
              let* () = write (AstHir.DeclVar (loc, true, x, Some rtype, None)) in
              let+ () = write (AstHir.Invoke(loc, Some x, id, el)) in 
              AstHir.Variable (loc, x)
      with Not_found -> failwith "call to undefined method"
      in aux e

  let buildSeq s1 s2 = AstHir.Seq (dummy_pos, s1, s2)

  let lower (c:in_body declaration_type) (env:TypeEnv.t) : out_body Error.result = 
    let open MonadSyntax(P) in
    let open MonadFunctions(P) in 
  let rec aux = function
    | l, AstParser.DeclVar (mut, id, t, e ) -> 
      begin match e with 
      | Some e -> let (e, s) = lower_expression env e in buildSeq s (AstHir.DeclVar (l, mut,id, t, Some e))
      | None -> AstHir.DeclVar (l, mut,id, t, None)
    end
    | l, AstParser.DeclSignal s -> AstHir.DeclSignal (l,s)
    | l, AstParser.Skip -> AstHir.Skip(l)
    | l, AstParser.Assign(e1, e2) -> 
      let (e1, s1) = lower_expression env e1 and (e2, s2) = lower_expression env e2 in
      AstHir.Seq (dummy_pos, s1, AstHir.Seq (dummy_pos, s2, AstHir.Assign(l, e1, e2)))
    | l, AstParser.Seq(c1, c2) -> AstHir.Seq(l, aux c1, aux c2) 
    | l, AstParser.Par(c1, c2) -> AstHir.Par(l, aux c1, aux c2)
    | l, AstParser.If(e, c1, Some c2) -> 
      let (e, s) = lower_expression env e in AstHir.Seq (dummy_pos, s,
       AstHir.If(l, e, aux c1, Some (aux c2)))
    | l, AstParser.If( e, c1, None) -> 
        let (e, s) = lower_expression  env e in AstHir.Seq (dummy_pos, s, AstHir.If(l, e, aux c1, None))
    | l, AstParser.While(e, c) -> 
      let (e,s) = lower_expression env e in buildSeq s (AstHir.While(l, e, aux c))
 (*   | AstParser.Case(loc, e, cases) -> AstHir.Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | l, AstParser.Case(e, _cases) -> 
      let (e,s) = lower_expression env e in  buildSeq s (AstHir.Case (l, e, []))
    | l, AstParser.Invoke(id, el) -> 
      let (el, s) = listMapM (lower_expression env) el in 
      buildSeq s (AstHir.Invoke(l, Some (freshVar ()), id, el))
    | l, AstParser.Return e -> 
        begin match e with 
        | None -> AstHir.Return(l, None)
        | Some e -> let (e,s) = lower_expression env e in buildSeq s (AstHir.Return(l, Some e))
      end
    | l, AstParser.Run(id, el) -> 
      let (el, s) = listMapM (lower_expression env) el in buildSeq s (AstHir.Run(l, id, el))
    | l, AstParser.Loop c -> AstHir.While(l, Literal(dummy_pos, LBool true) , aux c)
    | l, AstParser.Emit s -> AstHir.Emit(l,s)
    | l, AstParser.Await s -> AstHir.When(l, s, AstHir.Skip(dummy_pos))
    | l, AstParser.When (s, c) -> AstHir.When(l, s, aux c)
    | l, AstParser.Watching(s, c) -> AstHir.Watching(l, s, aux c)
    | l, AstParser.Block c -> AstHir.Block(l, aux c)
  in Result.ok (aux c.body)
end