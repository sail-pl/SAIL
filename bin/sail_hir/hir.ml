
open Common

let translate_statement (c : Ast_parser.statement) : Ast_hir.statement = 
  let rec aux c = 
  match c with 
    Ast_parser.DeclVar (loc, mut, id, t, e ) -> Ast_hir.DeclVar (loc, mut,id, t, e)
    | Ast_parser.DeclSignal(loc, s) -> Ast_hir.DeclSignal(loc, s)
    | Ast_parser.Skip (loc) -> Ast_hir.Skip(loc)
    | Ast_parser.Assign(loc, e1, e2) -> Ast_hir.Assign(loc, e1, e2)
    | Ast_parser.Seq(loc, c1, c2) -> Ast_hir.Seq(loc, aux c1, aux c2) 
    | Ast_parser.Par(loc, c1, c2) -> Ast_hir.Par(loc, aux c1, aux c2)
    | Ast_parser.If(loc, e, c1, Some c2) -> Ast_hir.If(loc, e, aux c1, Some (aux c2))
    | Ast_parser.If(loc, e, c1, None) -> Ast_hir.If(loc, e, aux c1, None)
    | Ast_parser.While(loc,e,c) -> Ast_hir.While(loc, e, aux c)
 (*   | Ast_parser.Case(loc, e, cases) -> Ast_hir.Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | Ast_parser.Case(loc, e, _cases) -> Ast_hir.Case (loc, e, [])
    | Ast_parser.Invoke(loc, id, id', el) -> Ast_hir.Invoke(loc, id, id',el)
    | Ast_parser.Return(loc, e) -> Ast_hir.Return(loc, e)
    | Ast_parser.Run(loc, id, el) -> Ast_hir.Run(loc, id, el)
    | Ast_parser.Loop(loc, c) -> Ast_hir.While(loc, Literal(loc, LBool true) , aux c) (* -> dummy lock *)
    | Ast_parser.Emit(loc, s) -> Ast_hir.Emit(loc,s)
    | Ast_parser.Await(loc, s) -> Ast_hir.When(loc, s, Ast_hir.Skip(loc)) (* -> dummy lock *)
    | Ast_parser.When(loc, s, c) -> Ast_hir.When(loc, s, aux c)
    | Ast_parser.Watching(loc, s, c) -> Ast_hir.Watching(loc, s, aux c)
    | Ast_parser.Block (loc, c) -> Ast_hir.Block(loc, aux c)
  in aux c

let translate_method (m : Ast_parser.statement Common.method_defn) : Ast_hir.statement Common.method_defn = 
  {
    m_pos = m.m_pos;
    m_name = m.m_name;
    m_generics = m.m_generics;
    m_params = m.m_params;
    m_rtype = m.m_rtype;
    m_body = translate_statement m.m_body
  }

let translate_process (p : Ast_parser.statement Common.process_defn) : Ast_hir.statement Common.process_defn =
  {
    p_pos = p.p_pos;
    p_name = p.p_name;
    p_generics = p.p_generics;
    p_interface = p.p_interface;
    p_body = translate_statement p.p_body
  }

let translate_module (m : Ast_parser.statement Common.sailModule) : Ast_hir.statement Common.sailModule = 
  {
    name = m.name; 
    structs = m.structs;
    enums = m.enums;
    methods = List.map translate_method m.methods;
    processes = List.map translate_process m.processes
  }
