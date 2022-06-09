
(* translate_expression should have a typing environment parameter *)

let translate_expression (e : Ast_parser.expression) : Ast_thir.expression = 
  failwith "TO DO"

let translate_statement (s : Ast_parser.expression Ast_hir.statement) : Ast_thir.expression Ast_hir.statement = 
  Ast_hir.Skip Lexing.dummy_pos

let translate_method (m : Ast_parser.expression Ast_hir.statement Common.method_defn) : Ast_thir.expression Ast_hir.statement Common.method_defn = 
  {
    m_pos = m.m_pos;
    m_name = m.m_name;
    m_generics = m.m_generics;
    m_params = m.m_params;
    m_rtype = m.m_rtype;
    m_body = translate_statement m.m_body
  }
  
let translate_process (p : Ast_parser.expression Ast_hir.statement Common.process_defn) : Ast_thir.expression Ast_hir.statement Common.process_defn =
  {
    p_pos = p.p_pos;
    p_name = p.p_name;
    p_generics = p.p_generics;
    p_interface = p.p_interface;
    p_body = translate_statement p.p_body
  }

let translate_module (m : Ast_parser.expression Ast_hir.statement Common.sailModule) : Ast_thir.expression Ast_hir.statement Common.sailModule = 
  {
    name = m.name; 
    structs = m.structs;
    enums = m.enums;
    methods = List.map translate_method m.methods;
    processes = List.map translate_process m.processes
  }