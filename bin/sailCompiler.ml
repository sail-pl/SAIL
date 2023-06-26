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

module C  = Constants
let error_handler err = "LLVM ERROR: " ^ err |> print_endline

open Monad.MonadSyntax(E) 
open Monad.MonadFunctions(E)
open Monad.MonadOperator(E) 
open MakeOrderedFunctions(ImportCmp) 

let moduleToIR (m:Mir.Pass.out_body SailModule.t) (dump_decl:bool) (verify_ir:bool) : llmodule E.t = 
  let llc = create_context () in
  let llm = create_module llc m.md.name in
  let* decls = get_declarations m llc llm in

  if dump_decl then failwith "not done yet";

  let env = SailEnv.empty decls in

  DeclEnv.iter_decls (fun name m -> let func = methodToIR llc llm m env name in if verify_ir then Llvm_analysis.assert_valid_function func) (Self Method) decls >>= fun () ->
  if verify_ir then 
    match Llvm_analysis.verify_module llm with 
    | None -> return llm 
    | Some reason -> E.throw @@ Error.make dummy_pos (Fmt.str "LLVM : %s" reason)
  else return llm

    

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


let link ?(is_lib = false) (llm:llmodule) (module_name : string) (basepath:string) (imports: string list) (libs : string list) (target, machine) clang_args : int =
  let f = Filename.(concat basepath module_name ^ C.object_file_ext) in
  let objfiles = String.concat " " (f::imports) in 
  let libs = List.map (fun l -> "-l " ^ l) libs |> String.concat " "  in 
  if Target.has_asm_backend target then
    begin
      Logs.info (fun m -> m "emitting object file...");
      TargetMachine.emit_to_file llm ObjectFile f machine;
      if not is_lib then 
        begin
        if (Option.is_none (lookup_function "main" llm)) then failwith ("no Main process found for module '" ^ module_name ^  "', can't compile as executable");
        let clang_cmd = Fmt.str "clang %s -o %s %s %s" objfiles module_name libs clang_args in
        Logs.debug (fun m -> m "invoking clang with the following parameters : \n%s" clang_cmd);
        Sys.command clang_cmd
        (* "rm " ^ objfile |>  Sys.command *)
        end
      else 0
    end
  else
    failwith ("target " ^ target_triple  llm ^ "doesn't have an asm backend, can't generate object file!")


let execute (llm:llmodule) = 
  (* 
    fixme : when depending on other modules, we need to 'Llvm_executionengine.add' them, which implies the .ll must be available to be read.
    This will be revisited when we make use of the .ll files for LTO 
  *)

  let _ = match lookup_function "main" llm with
  | Some m -> m
  | None -> failwith "can't execute : no main process found" 
  in
  match Llvm_executionengine.initialize () with
  | false -> failwith "unable to start the execution engine"
  | _ -> ();
  let ee = Llvm_executionengine.create llm in
  let open Ctypes in 
  let m_t = void @-> returning int in
  let main_addr = Llvm_executionengine.get_function_address "main" (static_funptr m_t) ee in 
  let main = coerce (static_funptr m_t) (Foreign.funptr m_t) main_addr in 
  let _ret = main () in 
  Llvm_executionengine.dispose ee (* implicitely disposes the module *)


let find_file_opt ?(maxdepth = 4) ?(paths = [Filename.current_dir_name]) (f:string)  : string option = (* recursively find the file *)
  let open Sys in 
  let open Filename in
  let rec aux dir depth = 
    if depth >= maxdepth then None 
    else
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
    | None ->  aux dir 0
    ) None paths



let sailor (files: string list) (intermediate:bool) (jit:bool) (noopt:bool) (dump_decl:bool) () (force_comp:bool list) (paths:string list) (is_lib : bool)  (clang_args: string) (verify_ir:bool) = 
  enable_pretty_stacktrace ();
  install_fatal_error_handler error_handler;

  let compile sail_module basepath is_lib : AstMir.mir_function SailModule.t E.t =
    let* m = return sail_module 
    |> Hir.Pass.transform 
    |> Thir.Pass.transform 
    |> MethodCall.Pass.transform
    |> Mir.Pass.transform 
    |> Imports.Pass.transform
    |> (if is_lib then Fun.id else MainProcess.Pass.transform)
    |> Monomorphization.Pass.transform

    in
    (* Out_channel.with_open_text Filename.(concat basepath m.md.name ^ ".mir.debug") (fun f -> Format.fprintf (Format.formatter_of_out_channel f) "%a" Pp_mir.ppPrintModule m); *)
    
    let+ llm = moduleToIR m dump_decl verify_ir in

    (* only generate mir file if codegen succeeds *)
    Out_channel.with_open_bin Filename.(concat basepath m.md.name ^ C.mir_file_ext) (fun f -> Marshal.to_channel f m []);

    let tm = init_llvm llm in

    if not noopt && not is_lib then 
      begin
        let open PassManager in
        let pm = create () in add_passes pm;
        let res = run_module llm pm in
        Logs.debug (fun m -> m "pass manager executed, module modified : %b" res);
        dispose pm
      end
    ;

    if intermediate then print_module Filename.(concat basepath m.md.name ^ C.llvm_ir_ext) llm;

    if not (intermediate || jit) then
      begin
        let libs,object_files = List.partition Filename.(fun e -> extension e <> C.object_file_ext) (FieldSet.elements m.md.libs) in 
        let imports = object_files @ List.map (fun i -> i.dir ^ i.mname ^ C.object_file_ext) @@ ImportSet.elements m.imports in
        let ret = link llm (sail_module.md.name) basepath imports libs tm ~is_lib clang_args in
        if ret <> 0 then
          (Fmt.str "clang couldn't execute properly (error %i)" ret |> failwith);
      end;
    if jit && not is_lib then execute llm else dispose_module llm;
    m
  in

  let rec process_file f (treated: string list) (compiling: (string*loc) list) ~is_lib : (string list * 'a SailModule.t) E.t = 
    let mname = Filename.(basename f |> remove_extension) in 
    let basepath = Filename.(dirname f) in 

    if List.mem mname treated then
     (Logs.debug (fun m -> m "skipping module '%s'" mname); 
      return (treated,SailModule.emptyModule))
    else
      let treated = mname::treated in 
      let add_imports_decls (curr_env: SailModule.DeclEnv.t ) (imports : ImportSet.t) = 
        ImportSet.fold (fun i -> 
          let file = i.dir ^ i.mname ^ C.mir_file_ext in 
          Logs.debug (fun m -> m "reading module '%s' from mir file %s" i.mname file); 
          let slmd : AstMir.mir_function SailModule.t = In_channel.with_open_bin file  Marshal.from_channel in
          (* Logs.debug (fun m -> m "decls of import %s : \n %s" i.mname (SailModule.DeclEnv.string_of_env slmd.declEnv)); *)
          SailModule.DeclEnv.add_import_decls (i, slmd.declEnv)
        )
        imports curr_env 
      in

      let* slmd = Parsing.parse_program f in 

      let process_imports_and_compile () : (string list * 'a SailModule.t) E.t =
        Logs.info (fun m -> m "======= processing module '%s' =======" slmd.md.name );
        Logs.debug (fun m -> m "module hash : %s" (Digest.to_hex slmd.md.hash));
        (* for each import, we check if a corresponding mir file exists.
          - if it exists, we get its corresponding sail_module 
          - if not, we look for a source file and compile it 
          we do not store the mir sail_module directly as the other passes are not aware of its signature
        *)  
        let* treated,imports = SetM.fold_left_map (
          fun treated (i : import ) -> 
            let* () = E.throw_if
            (
              let msg = 
              if i.mname = slmd.md.name then 
                "a module cannot import itself" 
              else 
              "dependency cycle : "  ^ (String.concat " -> " ((List.split compiling |> fst |> List.rev) @ [slmd.md.name;i.mname]))
              in Error.make i.loc msg
            )  (List.mem_assoc i.mname compiling) in         
            let mir_name = i.mname ^ C.mir_file_ext in
            let source = i.mname ^ C.sail_file_ext in
            
            let import = fun m -> {i with dir=Filename.(dirname m ^ dir_sep); proc_order=(List.length compiling)} in 

            match find_file_opt source ~paths:(Filename.current_dir_name::paths),find_file_opt mir_name with
            | Some s,Some m 
              when In_channel.with_open_bin m 
              (fun f -> 
                let mir : 'a SailModule.t = Marshal.from_channel f in 
                Digest.(equal mir.md.hash @@ file s) && 
                List.length force_comp < 2 &&
                mir.md.version = C.sailor_version
              )
              -> (* mir up-to-date with source -> use mir *)
              return (treated,import m)
            | None, Some m -> (* mir but no source -> use mir *)
              let mir :'a SailModule.t = In_channel.with_open_bin m Marshal.from_channel in
              E.throw_if 
              (Error.make dummy_pos @@ Printf.sprintf "module %s was compiled with sailor %s, current is %s" mir.md.name mir.md.version C.sailor_version)
              (mir.md.version <> C.sailor_version) 
              >>| fun () -> treated,import m
            | None,None -> (* nothing to work with *)
              E.throw @@ Error.make i.loc "import not found"
            | Some s, _ -> (* source but no mir or mir not up-to-date -> compile *)
              begin
              let+ treated',_mir = process_file s treated ((slmd.md.name,i.loc)::compiling) ~is_lib:true  
              in 
              treated',import s
              end 
          ) treated slmd.imports 
        in 
        let declEnv = add_imports_decls slmd.declEnv imports in
        (* SailModule.DeclEnv.print_declarations declEnv; *)
        let+ sm = compile {slmd with imports ; declEnv} basepath is_lib in
        Logs.info (fun m -> m "======= done processing module '%s' =======\n" slmd.md.name);
        treated,sm
      in

      let mir_file = Filename.(dirname f ^ dir_sep ^ slmd.md.name ^ C.mir_file_ext) in
      (* if mir file exists, check hash, if same hash, no need to compile *)
      if Sys.file_exists mir_file && (List.length force_comp = 0) then
        let mir : 'a SailModule.t = In_channel.with_open_bin mir_file Marshal.from_channel in
        let* () = E.throw_if (Error.make dummy_pos @@ Printf.sprintf "module %s was compiled with sailor %s, current is %s" mir.md.name mir.md.version C.sailor_version)
                  (mir.md.version <> C.sailor_version) 
        in
        if not @@ Digest.equal mir.md.hash slmd.md.hash then
          process_imports_and_compile () 
        else 
          begin
            Logs.app (fun m -> m "'%s' is up-to-date, use '-f' to force compilation" slmd.md.name);
            return (treated,mir)
          end
      else
        process_imports_and_compile ()
  in 

  try 
  match ListM.fold_left (fun t f -> let+ t,_ = process_file f t [] ~is_lib in f::t) [] files with
  | Ok treated,_ -> Logs.debug (fun m -> m "files processed : %s " @@ String.concat " " treated) ; `Ok ()
  | Error e,errs -> 
    Error.print_errors (e::errs);
    `Error(false, "compilation aborted") 
    
  with
  | e ->
      let msg = 
        if (Printexc.backtrace_status () |> not) then (
          Logs.warn (fun m -> m "backtrace recording is not turned on, only the exception name will be printed. To print the backtrace, run with 'OCAMLRUNPARAM=b'");
          Printexc.to_string e)
        else Printexc.get_backtrace () in 
     `Error (false,msg)

let jit_arg =
  let doc = "execute using the LLVM JIT compiler" in 
   Arg.(value & flag & info ["run"] ~doc)

let intermediate_arg = intermediate_arg "save the LLVM IR"

let noopt_arg = 
  let doc = "do not use any optimisation pass" in
  Arg.(value & flag & info ["no-opt"] ~doc)


let dump_decl_arg =
  let doc = "dump the declarations" in 
  let i = Arg.info ["D"; "dump_decl"] ~doc in
  Arg.(value & flag i)

let extra_paths =
  let doc = "add folders to look for modules" in 
  Arg.(value & (opt_all dir [] & info  ["L"] ~doc))

let force_comp =
  let doc = "force compilation. Repeat twice to also recursively recompile imports" in 
  let i = Arg.info ["f"; "force"] ~doc in
  Arg.(value & flag_all i)
  
let as_lib =
  let doc = "only generate object file" in 
  let i = Arg.info ["as-lib"] ~doc in
  Arg.(value & flag i)

let verify_ir =
  let doc = "assert generated LLVM IR is correct" in 
  let i = Arg.info ["verify_ir"] ~doc in
  Arg.(value & opt bool true i)
  

  
let clang_args = 
  let doc = "extra args to pass to clang" in 
  Arg.(value & opt string ""  & info  ["clang-args"] ~doc)

let cmd =
  let doc = "SaiLOR, the SaIL cOmpileR" in
  let info = Cmd.info "sailor" ~doc ~version:C.sailor_version in
  Cmd.v info Term.(ret (const sailor $ sailfiles_arg $ intermediate_arg $ jit_arg $ noopt_arg $ dump_decl_arg $ setup_log_term $ force_comp $ extra_paths $ as_lib $ clang_args $ verify_ir))

let () = Cmd.eval cmd |> exit
