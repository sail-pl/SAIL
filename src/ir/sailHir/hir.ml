
open Common
open Parser

let translate_statement (c :AstParser.statement) :  AstParser.expression AstHir.statement = 
  let rec aux c = 
  match c with 
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
    | AstParser.Loop(loc, c) -> AstHir.While(loc, Literal(loc, LBool true) , aux c) (* -> dummy lock *)
    | AstParser.Emit(loc, s) -> AstHir.Emit(loc,s)
    | AstParser.Await(loc, s) -> AstHir.When(loc, s, AstHir.Skip(loc)) (* -> dummy lock *)
    | AstParser.When(loc, s, c) -> AstHir.When(loc, s, aux c)
    | AstParser.Watching(loc, s, c) -> AstHir.Watching(loc, s, aux c)
    | AstParser.Block (loc, c) -> AstHir.Block(loc, aux c)
  in aux c

let translate_method (m : AstParser.statement TypesCommon.method_defn) : AstParser.expression AstHir.statement TypesCommon.method_defn = 
  {
    m_pos = m.m_pos;
    m_name = m.m_name;
    m_generics = m.m_generics;
    m_params = m.m_params;
    m_rtype = m.m_rtype;
    m_body = translate_statement m.m_body
  }

let translate_process (p : AstParser.statement TypesCommon.process_defn) : AstParser.expression AstHir.statement TypesCommon.process_defn =
  {
    p_pos = p.p_pos;
    p_name = p.p_name;
    p_generics = p.p_generics;
    p_interface = p.p_interface;
    p_body = translate_statement p.p_body
  }

let translate_module (m : AstParser.statement TypesCommon.sailModule) : AstParser.expression AstHir.statement TypesCommon.sailModule = 
  {
    name = m.name; 
    structs = m.structs;
    enums = m.enums;
    methods = List.map translate_method m.methods;
    processes = List.map translate_process m.processes
  }
