open Llvm
open Common.TypesCommon
open Common.Env
open CompilerCommon


module Declarations = struct
  type process_decl = unit
  type method_decl = IrMir.Mir.Pass.out_body method_defn * llvalue
  type struct_decl = unit
  type enum_decl = unit
end

module DeclEnv = DeclarationsEnv (Declarations)

module SailEnv = VariableDeclEnv (Declarations)(
  struct 
    type t = bool * sailtype * llvalue
    let string_of_var (_,t,_) = string_of_sailtype (Some t)

    let to_var (m:bool) (t:sailtype) = m,t,(() |> global_context |> i32_type |> const_null) (*fixme : make specialized var env for passes to not have this ugly thing *)

  end
) 

let declare_method (llc:llcontext) (llm:llmodule) (decls:DeclEnv.t) (m:Pass.out_body method_defn)  : DeclEnv.t = 
  let llvm_rt = match m.m_proto.rtype with
  | Some t -> getLLVMType t llc llm
  | None -> void_type llc
  in
  let args_type = List.map (fun (_,_,arg) -> getLLVMType arg llc llm) m.m_proto.params |> Array.of_list in
  let method_t = function_type llvm_rt args_type in
  let name' = if String.equal "_Main_" m.m_proto.name then "main" else  m.m_proto.name in
  let proto = declare_function name' method_t llm
  in DeclEnv.add_method decls  m.m_proto.name (m,proto)


let get_declarations (sm: IrMir.Mir.Pass.out_body Common.SailModule.t) llc llm : DeclEnv.t = 
  Logs.debug (fun m -> m "generating %i llvm functions" (List.length sm.methods));
  
  List.fold_left (declare_method llc llm) DeclEnv.empty sm.methods
  (* todo : enums & structs *)





