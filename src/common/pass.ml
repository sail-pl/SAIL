module type StatementPass = sig
  type in_body
  type out_body
  val translate : in_body -> out_body
end

module type S = sig
  type in_body
  type out_body
  val translate_module : in_body TypesCommon.sailModule -> out_body TypesCommon.sailModule
end


module Make (T: StatementPass) : S with 
                                  type in_body = T.in_body and 
                                  type out_body = T.out_body = 
struct
  type in_body = T.in_body
  type out_body = T.out_body

  let translate_method (m:T.in_body TypesCommon.method_defn) : T.out_body TypesCommon.method_defn = 
    {
      m_body = T.translate m.m_body;
      m_rtype = m.m_rtype;
      m_params = m.m_params;
      m_generics = m.m_generics;
      m_name = m.m_name;
      m_pos = m.m_pos;
    }

  let translate_process (p : T.in_body TypesCommon.process_defn) : T.out_body TypesCommon.process_defn =
    {
      p_pos = p.p_pos;
      p_name = p.p_name;
      p_generics = p.p_generics;
      p_interface = p.p_interface;
      p_body = T.translate p.p_body
    }

  let translate_module (m: T.in_body TypesCommon.sailModule) : T.out_body TypesCommon.sailModule = 
    {
      name = m.name;
      structs = m.structs;
      enums = m.enums;
      methods = List.map translate_method m.methods;
      processes = List.map translate_process m.processes;
    }
    
end