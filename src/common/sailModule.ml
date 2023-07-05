open TypesCommon
module E = Error.Logger

module Declarations = struct
  type process_decl = loc * function_proto
  type method_decl = l_str * function_proto 
  type struct_decl = loc * struct_proto
  type enum_decl = loc * enum_proto
  type type_decl = ty_defn
end

module DeclEnv = Env.DeclarationsEnv(Declarations)

module SailEnv = Env.VariableDeclEnv(Declarations) 


type ('m,'p) methods_processes  = {methods : 'm method_defn list ; processes : 'p process_defn list; }

type 'a t =
{
  declEnv: DeclEnv.t;
  builtins : method_sig list ;
  body : 'a;
  imports : ImportSet.t;
  md : metadata;
}

let emptyModule empty_content = 
{
  declEnv = DeclEnv.empty;
  builtins = [];
  body = empty_content;
  imports = ImportSet.empty;
  md = {
    name = String.empty; 
    version = String.empty;
    hash = String.empty; 
    libs = FieldSet.empty
  };
}

let method_decl_of_defn (d : 'a method_defn) : Declarations.method_decl = 
  let pos = d.m_proto.pos
  and name = (match d.m_body with Left (sname,_) -> sname | Right _ -> d.m_proto.name)
  and ret = d.m_proto.rtype 
  and args = d.m_proto.params 
  and generics = d.m_proto.generics 
  and variadic = d.m_proto.variadic in
  ((pos,name),{ret;args;generics;variadic})