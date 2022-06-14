open Llvm
open Common.TypesCommon
open Common.Env
open CompilerCommon


module Declarations = struct
  type process_decl = {ret:sailtype option; proto:llvalue}
  type method_decl = {ret:sailtype option; proto:llvalue}
  type struct_decl = unit
  type enum_decl = unit
end

module DeclEnv = DeclarationsEnv (Declarations)

module SailEnv = VariableEnv (
  struct 
    type t = sailtype * llvalue
    let string_of_var (t,_) = string_of_sailtype (Some t)
  end
) (DeclEnv)

let declare_method (llc:llcontext) (llm:llmodule) (name:string) (m:sailor_method) (decls:DeclEnv.t) : DeclEnv.t = 
  let llvm_rt = match m.decl.ret with
  | Some t -> getLLVMType t llc llm
  | None -> void_type llc
  in
  let args_type = List.map (fun (_,arg) -> getLLVMType arg llc llm) m.decl.args |> Array.of_list in
  let method_t = function_type llvm_rt args_type in
  let name' = if String.equal "_Main_" name then "main" else name in
  let proto = declare_function name' method_t llm
  in DeclEnv.add_declaration decls name (Method {ret=m.decl.ret;proto})


let get_declarations (funs:sailor_functions) llc llm : DeclEnv.t = 
  Logs.debug (fun m -> m "generating llvm declarations");
  FieldMap.fold (declare_method llc llm) funs (DeclEnv.empty ())
  (* todo : enums & structs *)





