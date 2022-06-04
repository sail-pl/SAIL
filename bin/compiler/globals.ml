open Common
open Llvm
open Compiler_common

type function_value = {ret:sailtype option; proto:llvalue; (* generics:sailor_args *)}
module type Globals = sig
  type t =  function_value FieldMap.t
  val get_declarations : sailor_callables -> llcontext -> llmodule -> t
  val find_declaration : t -> string -> function_value option

  val write_declarations : t -> string -> unit
end

  
module Globals : Globals = struct
  type t = function_value FieldMap.t
    
  let methods_globals (llc:llcontext) (llm:llmodule) (name:string) (m:sailor_method) (globals:t) : t = 
      let llvm_rt = match m.decl.ret with
      | Some t -> getLLVMType t llc llm
      | None -> void_type llc
      in
      let args_type = List.map (fun (_,arg) -> getLLVMType arg llc llm) m.decl.args |> Array.of_list in
      let method_t = function_type llvm_rt args_type in
      let proto = declare_function name method_t llm
      in FieldMap.add name {ret=m.decl.ret;proto} globals


  let processes_globals (llc:llcontext) (llm:llmodule) (name:string) (p: sailor_process) (globals:t) : t = 
    let args_type = List.map (fun (_,arg) -> getLLVMType arg llc llm) p.args |> Array.of_list in
    let process_t  = function_type (void_type llc) args_type in
    let name' = if String.equal "_Main_" name then "main" else name in
    let proto = declare_function name' process_t llm in
    FieldMap.add name {ret=None;proto} globals

  
  let get_declarations (sc:sailor_callables) llc llm : t = 
    Logs.debug (fun m -> m "generating llvm declarations");
    FieldMap.empty 
    |> fun g -> FieldMap.fold (methods_globals llc llm) sc.methodMap g
    |> fun g -> FieldMap.fold (processes_globals llc llm) sc.processMap g
    (* todo : enums & structs *)


    let find_declaration g name = 
      FieldMap.find_opt name g 


    let write_declarations (g:t) name = 
      (* todo : define a format to easily retrieve information *)
      let filename = name ^ ".sli" in
      let def_file = open_out filename in
      FieldMap.iter (fun _ {ret;_} -> output_string def_file (string_of_sailtype ret)) g;
      close_out def_file 
end