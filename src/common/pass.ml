open TypesCommon


type function_proto = 
{
  ret : sailtype option;
  args : (string * sailtype) list;
  generics : string list;
}

type enum_proto = 
{
  generics : string list;
  injections : (string * sailtype list) list;
}

type struct_proto = 
{
  generics : string list;
  fields : (string * sailtype) list
}


module DeclEnv = Env.DeclarationsEnv (
  struct
    type process_decl = function_proto
    type method_decl = function_proto 
    type struct_decl = struct_proto
    type enum_decl = enum_proto
  end
)

module TypeEnv = Env.VariableEnv(
  struct 
    type t = sailtype
    let string_of_var v = string_of_sailtype (Some v)
  end
) (
  DeclEnv
)

module type Body = sig
  type in_body
  type out_body
  val translate : in_body ->  TypeEnv.t  -> out_body
end


module type S = sig
  type in_body
  type out_body
  val translate_module : in_body sailModule -> out_body sailModule
end


module Make (T: Body) : S with type in_body = T.in_body and type out_body = T.out_body = 
struct
  type in_body = T.in_body
  type out_body = T.out_body


  let collect_declarations (m :T.in_body sailModule) : DeclEnv.t =
      (* todo: collect externals  *)
    DeclEnv.empty () |> fun d -> 

    List.fold_left (
      fun acc m -> 
        let ret = m.m_rtype 
        and args = m.m_params 
        and generics = m.m_generics in 
        DeclEnv.add_declaration acc m.m_name (Method {ret;args;generics})
    ) d m.methods |> fun d ->  

    List.fold_left (
      fun acc p -> 
        let ret = None
        and args = fst p.p_interface
        and generics = p.p_generics in 
        DeclEnv.add_declaration acc p.p_name (Process {ret;args;generics})
    ) d m.processes |> fun d -> 

    List.fold_left (
      fun acc s ->  
        DeclEnv.add_declaration acc s.s_name (Struct {generics=s.s_generics;fields=s.s_fields})
    ) d m.structs  |> fun d -> 

    List.fold_left (
      fun acc e ->  
        DeclEnv.add_declaration acc e.e_name (Enum {generics=e.e_generics;injections=e.e_injections})
    ) d m.enums 

  let get_start_env decls args =
    let env = TypeEnv.empty decls |> TypeEnv.new_frame in
    List.fold_left (fun m (n,t) -> TypeEnv.declare_var m n t) env args

  let translate_method (m:T.in_body method_defn) (decls : DeclEnv.t) : T.out_body method_defn = 
    let start_env = get_start_env decls m.m_params in
    { m with m_body = T.translate m.m_body start_env}

  let translate_process (p : T.in_body process_defn) (decls : DeclEnv.t) : T.out_body process_defn = 
    let start_env = get_start_env decls (p.p_interface |> fst) in
    { p with p_body = T.translate p.p_body start_env}

  let translate_module (m: T.in_body sailModule) : T.out_body sailModule = 
    let decls = collect_declarations m in
    {
      m with 
      methods = List.map (fun m -> translate_method m decls) m.methods ; 
      processes = List.map (fun p -> translate_process p decls) m.processes 
    }
    
end