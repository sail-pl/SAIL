open CliCommon
open Cmdliner
open Llvm
open Llvm_target
open Code_generator
open Sail_env
let error_handler err = "LLVM ERROR: " ^ err |> print_endline

let fileToIR (a : Ast.statement Common.sailModule) : llmodule  = 
  let llc = global_context () in
  let llm = create_module llc (a.name ^ ".sl") in
  let env = SailEnv.empty () in
  (* fixme : this forces an order of declaration ... *)
  List.iter (fun s -> parse_method s llc llm env) a.methods;
  List.iter (fun s -> parse_process s llc llm env) a.processes;
  match Llvm_analysis.verify_module llm with
  | None -> llm
  | Some reason -> print_endline reason; llm


let init_llvm (llm : llmodule) : (Target.t * TargetMachine.t) =
  Llvm_all_backends.initialize (); 
  let target_triple = Target.default_triple () in
  let target = Target.by_triple target_triple in 
  set_target_triple target_triple llm;
  let machine = TargetMachine.create ~triple:target_triple target ~reloc_mode:PIC in
  set_data_layout (TargetMachine.data_layout machine |> DataLayout.as_string) llm;
  (target,machine)


let run_pm (llm : llmodule) : unit = 
  let pm = PassManager.create () in 

  (* seems to be deprecated
    TargetMachine.add_analysis_passes pm machine; *)

  (* base needed for other passes *)
  Llvm_scalar_opts.add_memory_to_register_promotion pm;
  (* eleminates redundant values and loads *)
  Llvm_scalar_opts.add_gvn pm;
  (* reassociate binary expressions *)
  Llvm_scalar_opts.add_reassociation pm;
  (* dead code elimination, basic block merging and more *)
  Llvm_scalar_opts.add_cfg_simplification pm;

  PassManager.run_module llm pm |> ignore

let compile (llm:llmodule) (module_name : string) (target, machine) : int =
  let objfile = module_name ^ ".o" in 
  if Target.has_asm_backend target then
    begin
      TargetMachine.emit_to_file llm ObjectFile objfile machine;
      Sys.command ( "clang " ^ objfile ^ " -o " ^ module_name) |> ignore;
      "rm " ^ objfile |>  Sys.command
    end
  else
    failwith ("target " ^ target_triple  llm ^ "doesn't have an asm backend, can't generate object file!")


let execute (llm:llmodule) = 
  let _ = match lookup_function "main" llm with
  | Some m -> m
  | None -> failwith "can't execute : no main process found" 
  in
  match Llvm_executionengine.initialize () with
  | false -> failwith "unable to start the execution engine"
  | _ -> ();
  let ee = Llvm_executionengine.create llm in
  let open Ctypes in 
  let main_addr = Llvm_executionengine.get_function_address "main" (static_funptr (void @-> returning void)) ee in 
  let m_t =  (void @-> returning void) in
  let main  = coerce (static_funptr m_t) (Foreign.funptr m_t) main_addr
  in 
  main ();
  Llvm_executionengine.dispose ee (* implicitely disposes the module *)

let sailor (files: string list) (intermediate:bool) (jit:bool) (noopt:bool) () = 
  let rec aux = function
  | f::r -> 
    let file_r = open_in f in
    let lexbuf = Lexing.from_channel file_r in
    let module_name = Filename.chop_extension (Filename.basename f) in
    begin
      match parse_program lexbuf with
      | Ok p ->
        enable_pretty_stacktrace ();
        install_fatal_error_handler error_handler;

        let llm = p module_name |> fileToIR in
        let tm = init_llvm llm in

        if not noopt then run_pm llm;

        if intermediate then print_module (module_name ^ ".ll") llm;

        if not (intermediate || jit) then
          begin
            let ret = compile llm module_name tm in
            if ret <> 0 then
              (Printf.sprintf "clang couldn't execute properly (error %i)" ret |> failwith);
          end;

        if jit then execute llm else dispose_module llm;

        aux r
        
      | Error e ->`Error (false, e)
    end
  | [] -> `Ok ()
  
  in 
  try aux files with
  | e -> `Error (false,Printexc.to_string e)

let jit_arg =
  let doc = "execute using the LLVM JIT compiler" in 
   Arg.(value & flag & info ["run"] ~doc)

let intermediate_arg = intermediate_arg "save the LLVM IR"

let noopt_arg = 
  let doc = "do not use any optimisation pass" in
  Arg.(value & flag & info ["no-opt"] ~doc)
  
let cmd =
  let doc = "SaiLOR, the SaIL cOmpileR" in
  let info = Cmd.info "sailor" ~doc in
  Cmd.v info Term.(ret (const sailor $ sailfiles_arg $ intermediate_arg $ jit_arg $ noopt_arg $ setup_log_term))

let () = Cmd.eval cmd |> exit
