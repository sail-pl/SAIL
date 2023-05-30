open TypesCommon

module Declarations = struct
  type process_decl = loc * function_proto
  type method_decl = l_str * function_proto 
  type struct_decl = loc * struct_proto
  type enum_decl = loc * enum_proto
  type type_decl = ty_defn
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

let method_decl_of_defn (d : 'a method_defn) : Declarations.method_decl = 
  let pos = d.m_proto.pos
  and name = (match d.m_body with Left (sname,_) -> sname | Right _ -> d.m_proto.name)
  and ret = d.m_proto.rtype 
  and args = d.m_proto.params 
  and generics = d.m_proto.generics 
  and variadic = d.m_proto.variadic in
  ((pos,name),{ret;args;generics;variadic})
  

open Monad.MonadSyntax(Error.Logger)
let method_of_process (m : 'a t) (name:string) : 'a method_defn Error.Logger.t = 
  let+ p = Error.Logger.throw_if_none 
      (Error.make dummy_pos @@ "module '" ^ m.md.name ^ "' : no '" ^ name ^ "' process found")
      (List.find_opt (fun p -> p.p_name = name) m.processes) 
  in
  let m_proto = {pos=p.p_pos; name=String.lowercase_ascii p.p_name; generics = p.p_generics; params = fst p.p_interface; variadic=false; rtype=None} 
  and m_body = Either.right p.p_body in
  {m_proto;m_body}