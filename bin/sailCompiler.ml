open SailParser
open CliCommon
open Cmdliner
open Llvm
open Llvm_target
open Common
open IrThir
open IrHir
open IrMir
open Compiler
(* open CompilerCommon *)
open Codegen
open CompilerEnv
let error_handler err = "LLVM ERROR: " ^ err |> print_endline

let librairies = ref ""


let moduleToIR (name:string) (m:Mir.Pass.out_body SailModule.t) (dump_decl:bool) : llmodule  = 
  let module FieldMap = Map.Make (String) in

  let llc = global_context () in
  let llm = create_module llc (name ^ ".sl") in

  let decls = get_declarations m llc llm in

  if dump_decl then failwith "not done yet";

  let env = SailEnv.empty decls in

  DeclEnv.iter_methods (fun name m -> methodToIR llc llm m env name |> Llvm_analysis.assert_valid_function ) decls;

  match Llvm_analysis.verify_module llm with
  | None -> llm
  | Some reason -> Logs.err (fun m -> m "LLVM : %s" reason); llm


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
  Llvm_scalar_opts.add_cfg_simplification pm;
  
  Llvm_ipo.add_global_optimizer pm;
  Llvm_ipo.add_constant_merge pm;
  Llvm_ipo.add_function_inlining pm


let compile (llm:llmodule) (module_name : string) (target, machine) : int =
  let objfile = module_name ^ ".o" in 
  if Target.has_asm_backend target then
    begin
      TargetMachine.emit_to_file llm ObjectFile objfile machine;
      Sys.command ( "clang " ^ objfile ^ " -o " ^ module_name ^ !librairies) |> ignore;
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


let merge_together sm1 sm2 =
  let open SailModule in
  let merge_envs (e1:DeclEnv.t) (e2:DeclEnv.t) : DeclEnv.t = 
    let merge =TypesCommon.FieldMap.union
    in
    {
      methods = merge (fun _ _ _ -> failwith "declaration clash") e1.methods e2.methods;
      processes = merge (fun _ _ _ -> failwith "declaration clash") e1.processes e2.processes;
      structs = merge  (fun _ _ _ -> failwith "declaration clash") e1.structs e2.structs;
      enums = merge  (fun _ _ _ -> failwith "declaration clash")  e1.enums e2.enums;
    }
  in
  let open SailModule in
  let open Monad.MonadSyntax(Error.Logger) in
  let+ sm1 and* sm2 in
  let name = sm2.name 
  and declEnv = merge_envs sm1.declEnv sm2.declEnv
  and methods = sm1.methods @ sm2.methods
  and processes=sm1.processes @ sm2.processes in
  {name; declEnv; methods; processes}



let merge_modules sm = 
	let include_list = ["print_utils.sl";"print_utils_2.sl"] in (* temporary *)
	let rec aux = fun ilist sailm ->
		match ilist with
			| [] -> sailm
			| h :: t -> aux t (merge_together (Parsing.parse_program h |> snd) sailm)
	in aux include_list sm
	
	
let isSailFile (file: string) =
	if String.equal (Filename.extension file) ".sl" 
		then true 
		else (librairies := !librairies ^ (" -l" ^ (String.sub file prefix_size ((String.length file) - prefix_size))) ; false)



let sailor (files: string list) (intermediate:bool) (jit:bool) (noopt:bool) (dump_decl:bool) () = 
  enable_pretty_stacktrace ();
  install_fatal_error_handler error_handler;

  let rec aux = function
  | f::r -> 
    let module_name = Filename.chop_extension (Filename.basename f) in
    begin
        let fcontent,sail_module = Parsing.parse_program f in
        let sail_module = 
          merge_modules (*fcontent*) sail_module
          |> Hir.Pass.lower 
          |> Thir.Pass.lower 
          |> Mir.Pass.lower 
          |> CompilerCommon.Pass.lower 
        in
        begin

        match sail_module with
        | Ok m,errors ->

          Error.print_errors fcontent errors;

          let mir_debug = module_name ^ "_mir" |> open_out in
          Format.fprintf (Format.formatter_of_out_channel mir_debug) "%a" Pp_mir.ppPrintModule m;
          close_out mir_debug;

          let llm = moduleToIR module_name m dump_decl in
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
        | Error e, errlist -> Error.print_errors fcontent @@ e::errlist; `Error(false, "compilation aborted")
        end
            end
  | [] -> `Ok ()
  
  in 
  let sail_files = (List.filter isSailFile files) in
  try aux sail_files with
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
