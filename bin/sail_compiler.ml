open Sail_common
open Llvm
open Llvm_target
open Code_generator

let error_handler err = "LLVM ERROR: " ^ err |> print_endline

let fileToIR (a : Ast.statement Common.sailModule) : llmodule  = 
  let context = global_context () in
  let llm = create_module context (a.name ^ ".sl") in
  List.iter (fun s -> parse_method s llm context) a.methods;
  List.iter (fun s -> parse_process s llm context) a.processes;
  match Llvm_analysis.verify_module llm with
  | None -> llm
  | Some reason -> print_endline reason; llm

let command = 
  let open Core in
  Command.basic ~summary:"SaiLOR, the SaIL cOmpileR"
    Command.Let_syntax.( 
      let%map_open filename = Command.Param.(anon ("input files" %: sailfile_type))
      and verbose = verbose_param
      and jit = flag "-jit" no_arg ~doc:"run using the LLVM JIT compiler"
      and dump = flag "-intermediate" no_arg ~doc:"save the LLVM IR"
      and no_opt = flag "-no-opt" no_arg ~doc:"do not use any optimisation passes"
      in fun () -> 
        Logs.set_level verbose;
        Logs.set_reporter (Logs_fmt.reporter ());
        In_channel.with_file filename
           ~f:(fun x ->
              let module_name = Filename.chop_extension (Filename.basename filename) in
              let lexbuf = Lexing.from_channel x in
              match parse_program lexbuf with
              | Error(e) -> Error.raise e
              | Ok(p) -> 
                enable_pretty_stacktrace ();
                install_fatal_error_handler error_handler;
                let llm = fileToIR (p module_name) in

                Llvm_all_backends.initialize (); 
                let target_triple = Target.default_triple () in
                let target = Target.by_triple target_triple in 
                set_target_triple target_triple llm;
                let machine = TargetMachine.create ~triple:target_triple target ~reloc_mode:PIC in
                set_data_layout (TargetMachine.data_layout machine |> DataLayout.as_string) llm;

                if not (no_opt) then
                begin
                  let pm = PassManager.create () in 

                  (* seems to be deprecated
                    TargetMachine.add_analysis_passes pm machine; *)

                  (* base needed for other passes *)
                  Llvm_scalar_opts.add_memory_to_register_promotion pm;
                  (* eleminates redundant values and loads *)
                  Llvm_scalar_opts.add_gvn pm;
                  (* reassociate binary expressions *)
                  Llvm_scalar_opts.add_reassociation pm;
                  (* dead code eliminiation, basic block merging and more *)
                  Llvm_scalar_opts.add_cfg_simplification pm;

                  PassManager.run_module llm pm |> ignore
                end;

                if dump then print_module (module_name ^ ".ll") llm;


                begin
                let objfile = module_name ^ ".o" in 
                match Target.has_asm_backend target with
                 | true -> 
                    begin
                    TargetMachine.emit_to_file llm ObjectFile objfile machine;
                    Sys_unix.command ( "clang " ^ objfile ^ " -o " ^ module_name) |> ignore;
                    "rm " ^ objfile |>  Sys_unix.command |> ignore
                     end
                 | false ->
                    print_endline ("target " ^ target_triple ^ "doesn't have an asm backend, can't generate object file!")
                 end;

                if jit then 
                  
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
                  
                else 

                  dispose_module llm (* a module isn't disposed by itself*)

              )
    )

let main = 
  command |> Command_unix.run ~version:"0.1"