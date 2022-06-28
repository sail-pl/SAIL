open CliCommon
open Cmdliner
open Llvm
open Llvm_target
open Common
open IrThir
open IrHir
open IrMir
open Compiler
open CompilerCommon
open Codegen
open TypeChecker
open CompilerEnv
let error_handler err = "LLVM ERROR: " ^ err |> print_endline


let moduleToIR (name:string) (funs,exts : sailor_functions * sailor_external string_assoc) (dump_decl:bool) : llmodule  = 
  let module FieldMap = Map.Make (String) in

  let llc = global_context () in
  let llm = create_module llc (name ^ ".sl") in

  let globals = get_declarations funs llc llm in

  if dump_decl then failwith "not done yet";

  let env = SailEnv.empty globals in
  
  FieldMap.iter (fun name f  -> 
    let f = methodToIR llc llm env name f exts in
    Llvm_analysis.assert_valid_function f
    ) funs;
  
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


let add_passes (pm : [`Module] PassManager.t) : unit  = 
  (* seems to be deprecated
    TargetMachine.add_analysis_passes pm machine; *)

  (* base needed for other passes *)
  Llvm_scalar_opts.add_memory_to_register_promotion pm;
  (* eleminates redundant values and loads *)
  Llvm_scalar_opts.add_gvn pm;
  (* reassociate binary expressions *)
  Llvm_scalar_opts.add_reassociation pm;
  (* dead code elimination, basic block merging and more *)
  Llvm_scalar_opts.add_cfg_simplification pm


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

let sailor (files: string list) (intermediate:bool) (jit:bool) (noopt:bool) (dump_decl:bool) () = 
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

        let module HirPass = Pass.Make(Hir.Pass) in
        let module ThirPass = Pass.Make(Thir.Pass) in
        let module MirPass = Pass.Make(Mir.Pass) in

        let sail_module = Result.ok (p module_name) |> HirPass.lower_module |> ThirPass.lower_module in
        begin

        match sail_module with
        | Ok _ ->
          let funs = Result.ok (p module_name) |> HirPass.lower_module |> Result.get_ok |> type_check_module in (* fixme : this will be removed when mir is done*)
          let llm = moduleToIR module_name funs dump_decl in
          let tm = init_llvm llm in

          if not noopt then 
            begin
              let open PassManager in
              let pm = create () in add_passes pm;
              let res = run_module llm pm in
              Logs.debug (fun m -> m "pass manager executed, module modified : %b" res);
              dispose pm
            end
          ;

          if intermediate then print_module (module_name ^ ".ll") llm;

          if not (intermediate || jit) then
            begin
              let ret = compile llm module_name tm in
              if ret <> 0 then
                (Fmt.str "clang couldn't execute properly (error %i)" ret |> failwith);
            end;

          if jit then execute llm else dispose_module llm;

          aux r
        | Error errlist -> Error.print_errors errlist; `Error(false, "compilation aborted")
        end
        
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


let dump_decl_arg =
  let doc = "dump the declarations" in 
  let info = Arg.info ["D"; "dump_decl"] ~doc in
  Arg.flag info |> Arg.value
  
  
let cmd =
  let doc = "SaiLOR, the SaIL cOmpileR" in
  let info = Cmd.info "sailor" ~doc in
  Cmd.v info Term.(ret (const sailor $ sailfiles_arg $ intermediate_arg $ jit_arg $ noopt_arg $ dump_decl_arg $ setup_log_term))

let () = Cmd.eval cmd |> exit
