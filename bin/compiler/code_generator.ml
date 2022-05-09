open Compiler_common
open Sail_env
open Statements_gen
open Llvm

let methodToIR (method_proto : llvalue) (m_args : (llbuilder->llvalue) array) (p_body : Ast.statement) (llc:llcontext) (llm:llmodule) (env:SailEnv.t) : unit =
  let builder = builder llc in
  let bb = append_block llc "" method_proto in
  position_at_end bb builder;
  let env,args = Array.fold_left_map (
    fun env x -> 
      let v = x builder in 
      let new_env = SailEnv.declare_var env (value_name v) v in 
      (new_env,v)
    ) env m_args

  in Array.iteri (fun i arg -> build_store (param method_proto i) arg builder |> ignore ) args;
  let llvm_args = {c = llc; b = builder; m = llm} in
  statementToIR method_proto p_body llvm_args env;
  match block_terminator (insertion_block builder) with
  | Some _ -> ()
  | None when return_type (type_of method_proto) = void_type llc ->   
    (* allow not to have a return for void methods*)
    build_ret_void builder |> ignore
  | _ ->         
    (* there must always be a return if return type is not void *)
    failwith "ERROR : method doesn't always return !"

let processToIR (method_proto : llvalue) (p_body : Ast.statement) (llc:llcontext) (llm:llmodule) (env:SailEnv.t) : unit =
    let builder = builder llc in
    let bb = append_block llc "" method_proto in
    position_at_end bb builder;
    let llvm_args = {c = llc; b = builder; m = llm} in
    statementToIR method_proto p_body llvm_args env |> ignore;
    let bt = block_terminator (insertion_block builder) in
    if (Option.is_none bt) then
          build_ret_void builder |> ignore

let methodArgs (args: (string * Common.sailtype) list ) (llc:llcontext) (llm:llmodule) : (llbuilder->llvalue) array = 
    let llvalue_list = List.map (
      fun (name, t) -> 
        let  ty = getLLVMType t llc llm in
        build_alloca ty name
    ) args in
    Array.of_list llvalue_list


let parse_method (s : Ast.statement Common.method_defn) (llc:llcontext) (llm:llmodule) (env:SailEnv.t) : unit =
  let method_rt = match s.m_rtype with
  | Some t -> getLLVMType t llc llm
  | None -> void_type llc
  in
  let method_t = 
    let args_type = List.map (fun (_,arg) -> getLLVMType arg llc llm) s.m_params |> Array.of_list in
    function_type method_rt args_type 
  in
  let method_proto = match lookup_function s.m_name llm with
    | None -> declare_function s.m_name method_t llm
    | Some f -> 
      if block_begin f <> At_end f then
        "redefinition of method " ^  s.m_name |> failwith
      else f
  in 
  let args = methodArgs s.m_params llc llm in
    methodToIR method_proto args s.m_body llc llm env |> ignore;
    if not (Llvm_analysis.verify_function method_proto) then
      begin
      "problem with method " ^ s.m_name |> print_endline;
      dump_value method_proto
      end

let parse_process (s: Ast.statement Common.process_defn) (llc:llcontext) (llm:llmodule) (env:SailEnv.t)  : unit =
    let args : lltype Array.t = [||] in
    let name = if String.equal "Main" s.p_name then "main" else s.p_name in
    let process_t = function_type (void_type llc) args in
    let process_proto = match lookup_function name llm with
      | None -> declare_function name process_t llm
      | Some f -> 
        if block_begin f <> At_end f then
          failwith ("redefinition of process " ^  name)
        else f
    in 
    processToIR process_proto s.p_body llc llm env  |> ignore;
    if not (Llvm_analysis.verify_function process_proto) then
      begin
      "problem with method " ^ s.p_name |> print_endline;
      dump_value process_proto
      end
