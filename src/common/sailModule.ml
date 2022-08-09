open TypesCommon


module DeclEnv = Env.DeclarationsEnv( 
struct
  type process_decl = loc * function_proto
  type method_decl = loc * function_proto 
  type struct_decl = loc * struct_proto
  type enum_decl = loc * enum_proto
end
)

module SailEnv = Env.VariableDeclEnv(DeclEnv) 

type 'a t =
{
  name : string;
  declEnv: DeclEnv.t;
  methods : 'a method_defn list ;
  processes : 'a process_defn list;
}

type moduleSignature = unit t

let signatureOfModule m =
{
  m with
  methods = List.map (fun m -> {m with m_body=Either.right ()}) m.methods;
  processes = List.map (fun p-> {p with p_body=()}) m.processes
}