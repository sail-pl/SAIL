open TypesCommon

module Declarations = struct
  type process_decl = loc * function_proto
  type method_decl = loc * string * function_proto 
  type struct_decl = loc * struct_proto
  type enum_decl = loc * enum_proto
  type type_decl = ty_defn
  type builtin_decl = method_sig
end

module DeclEnv = Env.DeclarationsEnv(Declarations)

module SailEnv = Env.VariableDeclEnv(Declarations) 

type 'a t =
{
  declEnv: DeclEnv.t;
  methods : 'a method_defn list ;
  processes : 'a process_defn list;
  builtins : method_sig list ;
  imports : ImportSet.t;
  md : metadata;
}

type moduleSignature = unit t

let signatureOfModule m =
{
  m with
  methods = List.map (fun m -> {m with m_body=Either.right ()}) m.methods;
  processes = List.map (fun p-> {p with p_body=()}) m.processes
}

let emptyModule = 
{
  declEnv = DeclEnv.empty;
  methods = [];
  processes = [];
  builtins = [];
  imports = ImportSet.empty;
  md = {
    name = String.empty; 
    version = String.empty;
    hash = String.empty; 
    libs = FieldSet.empty
  };
}