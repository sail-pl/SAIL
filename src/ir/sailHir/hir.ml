
open Parser
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

    | AstParser.Variable (l,id) -> AstHir.Variable(l,id)
    | AstParser.Deref (l,e) -> AstHir.Deref(l, lower_expression e)
    | AstParser.ArrayRead (l,array_exp,idx) -> AstHir.ArrayRead(l,lower_expression array_exp, lower_expression idx)
    | AstParser.StructRead (l,struct_exp,field) -> AstHir.StructRead (l,lower_expression struct_exp,field)
    | AstParser.Literal (l,li) -> AstHir.Literal(l,li) 
    | AstParser.UnOp (l,op,e) -> AstHir.UnOp (l,op,lower_expression e)
    | AstParser.BinOp (l,op,le,re) -> AstHir.BinOp (l,op,lower_expression le,lower_expression re)
    | AstParser.Ref  (l,mut,e) -> AstHir.Ref(l,mut,lower_expression e)
    | AstParser.ArrayStatic (l,el) -> AstHir.ArrayStatic(l,List.map lower_expression el) 
    | AstParser.StructAlloc (l,name,fields) -> AstHir.StructAlloc (l,name,FieldMap.map lower_expression fields)
    | AstParser.EnumAlloc (l,name,el) -> AstHir.EnumAlloc (l,name,List.map lower_expression el)
    | AstParser.MethodCall (l,name,args) -> AstHir.MethodCall(l,name, List.map lower_expression args)


    let lower c _  = 
    let rec aux = function
      AstParser.DeclVar (loc, mut, id, t, e ) -> AstHir.DeclVar (loc, mut,id, t, fmap lower_expression e )
      | AstParser.DeclSignal(loc, s) -> AstHir.DeclSignal(loc, s)
      | AstParser.Skip (loc) -> AstHir.Skip(loc)
      | AstParser.Assign(loc, e1, e2) -> AstHir.Assign(loc, lower_expression e1, lower_expression e2)
      | AstParser.Seq(loc, c1, c2) -> AstHir.Seq(loc, aux c1, aux c2) 
      | AstParser.Par(loc, c1, c2) -> AstHir.Par(loc, aux c1, aux c2)
      | AstParser.If(loc, e, c1, Some c2) -> AstHir.If(loc,lower_expression e, aux c1, Some (aux c2))
      | AstParser.If(loc, e, c1, None) -> AstHir.If(loc, lower_expression e, aux c1, None)
      | AstParser.While(loc,e,c) -> AstHir.While(loc, lower_expression e, aux c)
  (*   | AstParser.Case(loc, e, cases) -> AstHir.Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
      | AstParser.Case(loc, e, _cases) -> AstHir.Case (loc, lower_expression e, [])
      | AstParser.Invoke(loc, id, id', el) -> AstHir.Invoke(loc, id, id', List.map lower_expression el)
      | AstParser.Return(loc, e) -> AstHir.Return(loc, fmap lower_expression e)
      | AstParser.Run(loc, id, el) -> AstHir.Run(loc, id,  List.map lower_expression el)
      | AstParser.Loop(loc, c) -> AstHir.While(loc, Literal(Lexing.dummy_pos, LBool true) , aux c)
      | AstParser.Emit(loc, s) -> AstHir.Emit(loc,s)
      | AstParser.Await(loc, s) -> AstHir.When(loc, s, AstHir.Skip(Lexing.dummy_pos))
      | AstParser.When(loc, s, c) -> AstHir.When(loc, s, aux c)
      | AstParser.Watching(loc, s, c) -> AstHir.Watching(loc, s, aux c)
      | AstParser.Block (loc, c) -> AstHir.Block(loc, aux c)
    in Result.ok (aux c.body)
end