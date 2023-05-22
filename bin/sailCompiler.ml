open SailParser
open CliCommon
open Cmdliner
open Llvm
open Llvm_target
open Common
open IrThir
open IrHir
open IrMir
open IrMisc
open Compiler
open TypesCommon
open Codegen
open CodegenEnv
let error_handler err = "LLVM ERROR: " ^ err |> print_endline


let moduleToIR (m:Mir.Pass.out_body SailModule.t) (dump_decl:bool) : llmodule  = 
  let llc = global_context () in
  let llm = create_module llc m.md.name in

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


let link ?(is_lib = false) (llm:llmodule) (module_name : string) (imports: string list) (libs : string list) (target, machine) : int =
  let mname = module_name ^ ".o" in 
  let objfiles = String.concat " " (mname::imports) in 
  let libs = List.map (fun l -> "-l " ^ l) libs |> String.concat " "  in 
  if Target.has_asm_backend target then
    begin
      TargetMachine.emit_to_file llm ObjectFile (module_name ^ ".o") machine;
      if not is_lib then 
        begin
        if (Option.is_none (lookup_function "main" llm)) then failwith ("no Main process found for module '" ^ module_name ^  "', can't compile as executable");
        let clang_cmd = "clang " ^ objfiles ^ " -o " ^ module_name ^ " " ^ libs in
        Logs.debug (fun m -> m "invoking clang with the following parameters : \n%s" clang_cmd);
        Sys.command clang_cmd
        (* "rm " ^ objfile |>  Sys.command *)
        end
      else 0
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


let find_file_opt ?(maxdepth = 4) ?(paths = ["."]) (f:string)  : string option = (* recursively find the file *)
  let open Sys in 
  let open Filename in
  let rec aux dir depth = 
    if depth > maxdepth then None else
      let dirs,files = readdir dir |> Array.to_list |> List.map (concat dir) |> List.partition is_directory 
      in
      match List.find_opt (fun f' -> String.equal f (basename f')) files with
      | Some f -> Some f
      | None -> List.fold_left (
          fun r d -> match r with 
          | Some f -> Some f 
          | None -> aux d (depth+1)
        ) None dirs
  in 
  List.fold_left (
    fun r dir -> match r with 
    | Some f -> Some f
    | None ->  aux dir maxdepth
    ) None paths


let sailor (files: string list) (intermediate:bool) (jit:bool) (noopt:bool) (dump_decl:bool) () (force_comp:bool list) (paths:string list) (is_lib : bool)= 
  let open Monad.MonadSyntax(Error.Logger) in
  let open Monad.MonadFunctions(Error.Logger) in
  let open MakeOrderedFunctions(ImportCmp) in

  enable_pretty_stacktrace ();
  install_fatal_error_handler error_handler;

  let compile sail_module is_lib : AstMir.mir_function SailModule.t Error.Logger.t =
    let+ m = return sail_module 
    |> Hir.Pass.transform 
    |> Thir.Pass.transform 
    |> MethodCall.Pass.transform
    |> Mir.Pass.transform 
    |> Imports.Pass.transform
    |> (if is_lib then Fun.id else MainProcess.Pass.transform)
    |> Monomorphization.Pass.transform
    (* |> (Fun.flip Error.Logger.get_warnings) Error.print_errors *)
    (* |> (Fun.flip Error.Logger.get_error (fun e -> Error.print_errors [e])) *)

    in
    Out_channel.with_open_bin (m.md.name ^ ".mir") (fun f -> Marshal.to_channel f m []);
    (* Out_channel.with_open_text (m.md.name ^ ".mir.debug") (fun f -> Format.fprintf (Format.formatter_of_out_channel f) "%a" Pp_mir.ppPrintModule m); *)
    
    let llm = moduleToIR m dump_decl in
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

    if intermediate then print_module (m.md.name ^ ".ll") llm;

    if not (intermediate || jit) then
      begin
        let libs = FieldSet.elements m.md.libs in 
        let imports = List.map (fun i -> i.dir ^ i.mname ^ ".o") @@ ImportSet.elements m.imports in
        let ret = link llm sail_module.md.name imports libs tm ~is_lib in
        if ret <> 0 then
          (Fmt.str "clang couldn't execute properly (error %i)" ret |> failwith);
      end;
    if jit && not is_lib then execute llm else dispose_module llm;
    m
  in

  let rec process_file f (treated: (string*loc) list) ~is_lib : 'a SailModule.t Error.Logger.t = 
    let add_imports_decls (curr_env: SailModule.DeclEnv.t ) (imports : MSet.t) = 
      MSet.fold (fun i e -> 
        let file = i.dir ^ i.mname ^ ".mir" in 
        Logs.debug (fun m -> m "reading module '%s' from mir file %s" i.mname file); 
        let slmd : AstMir.mir_function SailModule.t = In_channel.with_open_bin file  Marshal.from_channel in
        SailModule.DeclEnv.add_import_decls e (i,slmd.declEnv)
      )
     imports curr_env 
    in

    let* slmd = Parsing.parse_program f in 

    let process_imports_and_compile () : 'a SailModule.t Error.Logger.t =
      Logs.info (fun m -> m "processing module '%s'" slmd.md.name );
      Logs.debug (fun m -> m "module hash : %s" (Digest.to_hex slmd.md.hash));
      (* for each import, we check if a corresponding mir file exists.
        - if it exists, we get its corresponding sail_module 
        - if not, we look for a source file and compile it 
         we do not store the mir sail_module directly as the other passes are not aware of its signature
      *)  
      let* imports = setMapM (
        fun (i : import ) -> 
          let* () = Error.Logger.throw_if (List.mem_assoc i.mname treated)
          (
            if i.mname = slmd.md.name then 
              Error.make i.loc "a module cannot import itself" 
            else 
              Error.make i.loc @@ "dependency cycle : "  ^ (String.concat " -> " ((List.split treated |> fst |> List.rev) @ [slmd.md.name;i.mname]))
          ) 
          in
          let mir_name = i.mname ^ ".mir" in
          let source = i.mname ^ ".sl" in

          match find_file_opt source ~paths:("."::paths),find_file_opt mir_name with
          | Some s,Some m 
            when In_channel.with_open_bin m 
            (fun f -> 
              let mir : 'a SailModule.t = Marshal.from_channel f in 
              Digest.(equal mir.md.hash @@ file s) && List.length force_comp < 2
            )
            -> (* mir up-to-date with source -> use mir *)
            return {i with dir=Filename.(dirname m ^ dir_sep)} 
          | None, Some m -> (* mir but no source -> use mir *) 
            return {i with dir=Filename.(dirname m ^ dir_sep)} 
          | None,None -> (* nothing to work with *)
            Error.Logger.throw @@ Error.make i.loc "import not found"
          | Some s, _ -> (* source but no mir or mir not up-to-date -> compile *)
            begin
            let+ _mir = process_file s ((slmd.md.name,i.loc)::treated) ~is_lib:true  
            in 
            {i with dir=Filename.(dirname s ^ dir_sep)}
            end 
        ) slmd.imports in 
        let declEnv = add_imports_decls slmd.declEnv imports in
        (* SailModule.DeclEnv.print_declarations declEnv; *)
        compile {slmd with imports ; declEnv} is_lib
    in

    let mir_file = Filename.(dirname f ^ dir_sep ^ slmd.md.name ^ ".mir") in
    (* if mir file exists, check hash, if same hash, no need to compile *)
    if Sys.file_exists mir_file && List.length force_comp = 0 then
      let mir : 'a SailModule.t = In_channel.with_open_bin mir_file Marshal.from_channel in
        if not @@ Digest.equal mir.md.hash slmd.md.hash then
        process_imports_and_compile ()
        else 
          begin
            Logs.app (fun m -> m "'%s' is up-to-date, use '-f' to force compilation" slmd.md.name);
            return mir
          end
    else
      process_imports_and_compile ()
    
  in 

  try 
  match listIterM (fun f -> let+ _mir = process_file f [] ~is_lib  in ()) files with
  | Ok _,_ -> `Ok ()
  | Error e,errs -> 
    Error.print_errors (e::errs);
    `Error(false, "compilation aborted") 
    
  with
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

let extra_paths =
  let doc = "add folders to look for modules" in 
  Arg.(value & (opt_all dir [] & info  ["L"] ~doc))

let force_comp =
  let doc = "force compilation. Repeat twice to also recursively recompile imports" in 
  let info = Arg.info ["f"; "force"] ~doc in
  Arg.flag_all info |> Arg.value
  
let as_lib =
  let doc = "only generate object file" in 
  let info = Arg.info ["as-lib"] ~doc in
  Arg.flag info |> Arg.value

  
let cmd =
  let doc = "SaiLOR, the SaIL cOmpileR" in
  let info = Cmd.info "sailor" ~doc in
  Cmd.v info Term.(ret (const sailor $ sailfiles_arg $ intermediate_arg $ jit_arg $ noopt_arg $ dump_decl_arg $ setup_log_term $ force_comp $ extra_paths $ as_lib))

let () = Cmd.eval cmd |> exit
