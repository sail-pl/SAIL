
open Parser
open IrHir
open Common


(* translate_expression should have a typing environment parameter *)

let translate_expression (_e : AstParser.expression) : AstThir.expression = 
  failwith "TO DO"

let translate_statement (_s : AstParser.expression AstHir.statement) : AstThir.expression AstHir.statement = 
  AstHir.Skip Lexing.dummy_pos

let translate_method (m : AstParser.expression AstHir.statement TypesCommon.method_defn) : AstThir.expression AstHir.statement TypesCommon.method_defn = 
  {
    m_pos = m.m_pos;
    m_name = m.m_name;
    m_generics = m.m_generics;
    m_params = m.m_params;
    m_rtype = m.m_rtype;
    m_body = translate_statement m.m_body
  }
  
let translate_process (p : AstParser.expression AstHir.statement TypesCommon.process_defn) : AstThir.expression AstHir.statement TypesCommon.process_defn =
  {
    p_pos = p.p_pos;
    p_name = p.p_name;
    p_generics = p.p_generics;
    p_interface = p.p_interface;
    p_body = translate_statement p.p_body
  }

let translate_module (m : AstParser.expression AstHir.statement TypesCommon.sailModule) : AstThir.expression AstHir.statement TypesCommon.sailModule = 
  {
    name = m.name; 
    structs = m.structs;
    enums = m.enums;
    methods = List.map translate_method m.methods;
    processes = List.map translate_process m.processes
  }