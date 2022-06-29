
open Parser
open Common.Pass


module Pass : Body with
              type in_body = AstParser.statement and   
              type out_body = AstParser.expression AstHir.statement = 
struct
  type in_body = AstParser.statement
  type out_body = AstParser.expression AstHir.statement

  let lower c _  = 
  let rec aux = function
    AstParser.DeclVar (loc, mut, id, t, e ) -> AstHir.DeclVar (loc, mut,id, t, e)
    | AstParser.DeclSignal(loc, s) -> AstHir.DeclSignal(loc, s)
    | AstParser.Skip (loc) -> AstHir.Skip(loc)
    | AstParser.Assign(loc, e1, e2) -> AstHir.Assign(loc, e1, e2)
    | AstParser.Seq(loc, c1, c2) -> AstHir.Seq(loc, aux c1, aux c2) 
    | AstParser.Par(loc, c1, c2) -> AstHir.Par(loc, aux c1, aux c2)
    | AstParser.If(loc, e, c1, Some c2) -> AstHir.If(loc, e, aux c1, Some (aux c2))
    | AstParser.If(loc, e, c1, None) -> AstHir.If(loc, e, aux c1, None)
    | AstParser.While(loc,e,c) -> AstHir.While(loc, e, aux c)
 (*   | AstParser.Case(loc, e, cases) -> AstHir.Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | AstParser.Case(loc, e, _cases) -> AstHir.Case (loc, e, [])
    | AstParser.Invoke(loc, id, id', el) -> AstHir.Invoke(loc, id, id',el)
    | AstParser.Return(loc, e) -> AstHir.Return(loc, e)
    | AstParser.Run(loc, id, el) -> AstHir.Run(loc, id, el)
    | AstParser.Loop(loc, c) -> AstHir.While(loc, Literal(Lexing.dummy_pos, LBool true) , aux c)
    | AstParser.Emit(loc, s) -> AstHir.Emit(loc,s)
    | AstParser.Await(loc, s) -> AstHir.When(loc, s, AstHir.Skip(Lexing.dummy_pos))
    | AstParser.When(loc, s, c) -> AstHir.When(loc, s, aux c)
    | AstParser.Watching(loc, s, c) -> AstHir.Watching(loc, s, aux c)
    | AstParser.Block (loc, c) -> AstHir.Block(loc, aux c)
  in Result.ok (aux c.body)
end