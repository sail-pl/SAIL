open TypesCommon
module E = Logging.Logger

module Declarations = struct
  type process_decl = loc * process_proto
  type method_decl = l_str * method_proto 
  type struct_decl = loc * struct_proto
  type enum_decl = loc * enum_proto
  type type_decl = ty_defn
end

module DeclEnv = Env.DeclarationsEnv(Declarations)

module SailEnv = Env.VariableDeclEnv(Declarations) 

module TypeMap = Map.Make(struct type t = loc let compare = compare end)

type ('m,'p) methods_processes  = {methods : 'm method_defn list ; processes : 'p process_defn list; }

type 'a t =
{
  typeEnv: Env.TypeEnv.t; (* create functions for each type to create if not exist entry to map (otherwise gives same id )*)
  declEnv: DeclEnv.t;
  builtins : method_sig list ;
  body : 'a;
  imports : ImportSet.t;
  md : metadata;
}

let emptyModule empty_content = 
{
  typeEnv = Env.TypeEnv.empty;
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