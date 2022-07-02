open SailParser
open Common.Pass
open Common.TypesCommon
open Common.Option.MonadOption


type expression = loc AstHir.expression

 module Pass : Body with
              type in_body = AstParser.statement and   
              type out_body = expression AstHir.statement =  
struct
  type in_body = AstParser.statement
  type out_body = expression AstHir.statement

  let rec lower_expression = function 
    | l, AstParser.Variable id -> AstHir.Variable(l,id)
    | l, AstParser.Deref e -> AstHir.Deref(l, lower_expression e)
    | l, AstParser.ArrayRead (array_exp,idx) -> AstHir.ArrayRead(l,lower_expression array_exp, lower_expression idx)
    | l, AstParser.StructRead (struct_exp,field) -> AstHir.StructRead (l,lower_expression struct_exp,field)
    | l, AstParser.Literal li -> AstHir.Literal(l,li) 
    | l, AstParser.UnOp (op,e) -> AstHir.UnOp (l,op,lower_expression e)
    | l, AstParser.BinOp (op,le,re) -> AstHir.BinOp (l,op,lower_expression le,lower_expression re)
    | l, AstParser.Ref  (mut,e) -> AstHir.Ref(l,mut,lower_expression e)
    | l, AstParser.ArrayStatic (el) -> AstHir.ArrayStatic(l,List.map lower_expression el) 
    | l, AstParser.StructAlloc (name,fields) -> AstHir.StructAlloc (l,name,FieldMap.map lower_expression fields)
    | l, AstParser.EnumAlloc (name,el) -> AstHir.EnumAlloc (l,name,List.map lower_expression el)
    | l, AstParser.MethodCall (name,args) -> AstHir.MethodCall(l,name, List.map lower_expression args)


    let lower c _  = 
    let rec aux = function
      | l, AstParser.DeclVar (mut, id, t, e ) -> AstHir.DeclVar (l, mut,id, t, fmap lower_expression e )
      | l, AstParser.DeclSignal(s) -> AstHir.DeclSignal(l, s)
      | l, AstParser.Skip -> AstHir.Skip(l)
      | l, AstParser.Assign(e1, e2) -> AstHir.Assign(l, lower_expression e1, lower_expression e2)
      | l, AstParser.Seq(c1, c2) -> AstHir.Seq(l, aux c1, aux c2) 
      | l, AstParser.Par(c1, c2) -> AstHir.Par(l, aux c1, aux c2)
      | l, AstParser.If(e, c1, Some c2) -> AstHir.If(l,lower_expression e, aux c1, Some (aux c2))
      | l, AstParser.If( e, c1, None) -> AstHir.If(l, lower_expression e, aux c1, None)
      | l, AstParser.While(e,c) -> AstHir.While(l, lower_expression e, aux c)
  (*  | l,  AstParser.Case(l, e, cases) -> AstHir.Case (l, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
      | l, AstParser.Case(e, _cases) -> AstHir.Case (l, lower_expression e, [])
      | l, AstParser.Invoke(id, el) -> AstHir.Invoke(l, id, List.map lower_expression el)
      | l, AstParser.Return e -> AstHir.Return(l, fmap lower_expression e)
      | l, AstParser.Run(id, el) -> AstHir.Run(l, id,  List.map lower_expression el)
      | l, AstParser.Loop c -> AstHir.While(l, Literal(dummy_pos, LBool true) , aux c)
      | l, AstParser.Emit s -> AstHir.Emit(l,s)
      | l, AstParser.Await s  -> AstHir.When(l, s, AstHir.Skip(dummy_pos))
      | l, AstParser.When (s, c) -> AstHir.When(l, s, aux c)
      | l, AstParser.Watching(s, c) -> AstHir.Watching(l, s, aux c)
      | l, AstParser.Block c -> AstHir.Block(l, aux c)
    in Result.ok (aux c.body)
end