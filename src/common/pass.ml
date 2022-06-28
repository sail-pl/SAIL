open TypesCommon
open Error



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
  val lower : in_body ->  TypeEnv.t  -> string list -> out_body result
end


module type S = sig
  type in_body
  type out_body
  val lower_module : in_body sailModule result -> out_body sailModule result
end


module Make (T: Body) : S with type in_body = T.in_body and type out_body = T.out_body = 
struct
  open Monad.MonadSyntax(Error.MonadError)
  
  type in_body = T.in_body
  type out_body = T.out_body


  let collect_declarations (m :T.in_body sailModule) : DeclEnv.t =

    let register_external  name ret args generics (env:DeclEnv.t)  : DeclEnv.t  = 
    let args = List.mapi (fun i t -> (string_of_int i,t)) args  in
    DeclEnv.add_declaration env name (Method {ret;args;generics})
    in

    DeclEnv.empty () |> fun d -> 

    List.fold_left (
      fun acc m -> 
        let ret = m.m_proto.rtype 
        and args = m.m_proto.params 
        and generics = m.m_proto.generics in 
        DeclEnv.add_declaration acc m.m_proto.name (Method {ret;args;generics})
    ) d m.methods |> fun d ->  

    List.fold_left (
      fun acc m -> 
        let ret = m.rtype 
        and args = m.params 
        and generics = m.generics in 
        DeclEnv.add_declaration acc m.name (Method {ret;args;generics})
    ) d m.ffi 
      
    (* fixme : generalize *)
    |> register_external "print_int"  None [Int] [] 
    |> register_external "print_newline"  None [] []
    |> register_external "print_string"  None [String] []
    |> register_external "printf"  None [String; GenericType "T"] ["T"]


    |> fun d ->

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
    List.fold_left (fun m (n,t) -> let* m in TypeEnv.declare_var m n t Lexing.dummy_pos) (Result.ok env) args

  let lower_method (m:T.in_body method_defn) (decls : DeclEnv.t) : T.out_body method_defn result = 
    let* start_env = get_start_env decls m.m_proto.params in
    let+ m_body =  T.lower m.m_body start_env m.m_proto.generics in
    { m with m_body}

  let lower_process (p : T.in_body process_defn) (decls : DeclEnv.t) : T.out_body process_defn result= 
    let* start_env = get_start_env decls (p.p_interface |> fst) in
    let+ p_body = T.lower p.p_body start_env p.p_generics in
    { p with p_body}

    
  let lower_module (m: T.in_body sailModule result) : T.out_body sailModule result = 
    let* m in
      let decls = collect_declarations m in
      (* DeclEnv.print_declarations decls; *)
      let methods,m_errors = partition_result (Fun.flip lower_method decls) m.methods
      and processes,p_errors = partition_result (Fun.flip lower_process decls) m.processes in

      let errors = m_errors @ p_errors in
      if errors = [] then
        Ok {m with  methods; processes}    
      else
        Error errors
end