open Compiler_common
open Sail_env
open Common
open Statements_gen
open Llvm

(* todo generalise method / process  *)
let constructMethod (method_proto : llvalue) (m_args : (sailtype * llvalue) array) (m_generics:sailor_args) (p_body : Ast.statement) (llvm:llvm_args) (env:SailEnv.t) : unit =
  let new_env,args = Array.fold_left_map (
    fun env tyvar -> 
      let new_env = SailEnv.declare_var env (value_name (snd tyvar)) tyvar in 
      (new_env, snd tyvar)
    ) env m_args 
  in Array.iteri (fun i arg -> build_store (param method_proto i) arg llvm.b |> ignore ) args;
  
  statementToIR method_proto p_body m_generics llvm new_env;
  let ret_ty = (type_of method_proto |> return_type |> subtypes).(0) in
  match block_terminator (insertion_block llvm.b) with
  (* assuming the builder is on the last block of the method *)
  | Some _ -> ()
  | None when classify_type ret_ty = TypeKind.Void ->   
    (* allow not to have a return for void methods*)
    build_ret_void llvm.b |> ignore
  | _ ->         
    (* there must always be a return if return type is not void *)
    failwith "ERROR : method doesn't always return !"


let constructProcess (process_proto : llvalue) (p_args : (sailtype * llvalue) array) (p_generics: sailor_args) (p_body : Ast.statement) (llvm:llvm_args) (env:SailEnv.t) : unit =
  let new_env,args = Array.fold_left_map (
    fun env tyvar -> 
      let new_env = SailEnv.declare_var env (value_name (snd tyvar)) tyvar in 
      (new_env, snd tyvar)
    ) env p_args 
  in
  Array.iteri (fun i arg -> build_store (param process_proto i) arg llvm.b |> ignore ) args;

  statementToIR process_proto p_body p_generics llvm new_env |> ignore;

  let bt = block_terminator (insertion_block llvm.b) in
  if (Option.is_none bt) then
        build_ret_void llvm.b |> ignore 


let toLLVMArgs (args: (string * Common.sailtype) list ) (llvm:llvm_args) : (sailtype * llvalue) array = 
  let llvalue_list = List.map (
    fun (name, t) -> 
      let ty = getLLVMType t llvm.c llvm.m in 
      t,build_alloca ty name llvm.b
  ) args in
  Array.of_list llvalue_list


let methodToIR (llc:llcontext) (llm:llmodule) (env:SailEnv.t) (name : string) (m : sailor_method) : unit =
  let builder = builder llc in
  let llvm = {b=builder; c=llc ; m = llm} in
  match SailEnv.get_method env name with
  | None -> Printf.sprintf "method %s doesn't exist !" name |> failwith
  | Some {ret=_;proto} -> 
      if block_begin proto <> At_end proto then
        failwith ("redefinition of method " ^  name);

      let bb = append_block llvm.c "" proto in
      position_at_end bb llvm.b;
      let args = toLLVMArgs m.decl.args llvm in
      constructMethod proto args m.generics m.body llvm env |> ignore;

      if not (Llvm_analysis.verify_function proto) then
        begin
        "problem with method " ^ name |> print_endline;
        dump_value proto
        end

let processToIR (llc:llcontext) (llm:llmodule) (env:SailEnv.t)  (name : string) (p : sailor_process) : unit =
  let builder = builder llc in
  let llvm = {b=builder; c=llc ; m = llm} in
  match SailEnv.get_method env name with
  | None -> Printf.sprintf "process %s doesn't exist !" name |> failwith
  | Some {ret=_;proto} -> 
      if block_begin proto <> At_end proto then
        failwith ("redefinition of process " ^  name);

    let bb = append_block llvm.c "" proto in
    position_at_end bb llvm.b;
    let args = toLLVMArgs p.args llvm in
    constructProcess proto args p.generics p.body llvm env  |> ignore;
    if not (Llvm_analysis.verify_function proto) then
      begin
      "problem with process " ^ name |> print_endline;
      dump_value proto
      end