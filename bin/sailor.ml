open Common
open TypesCommon
open SailParser
module E = Error.Logger
module Const  = Constants
module C = Codegen

(* llvm *)
module L = Llvm
module T = Llvm_target


(* passes *)
module ProcessPass = ProcessPass.Process.Pass
module Hir = IrHir.Hir.Pass
module Thir = IrThir.Thir.Pass
module Mir = IrMir.Mir.Pass
module Imports = Misc.Imports.Pass
module MCall = Misc.MethodCall.Pass
module Mono = Mono.Monomorphization.Pass

(* error handling *)
open Monad.UseMonad(E)

let apply_passes (sail_module : Hir.in_body SailModule.t) (comp_mode : Cli.comp_mode) : Mono.out_body SailModule.t E.t =
  let hir_debug =  fun m -> let+ m in Out_channel.with_open_text (sail_module.md.name ^ ".hir.debug") (fun f -> Format.(fprintf (formatter_of_out_channel f)) "%a" IrHir.Pp_hir.ppPrintModule m); m in
  let mir_debug =  fun m -> let+ m in Out_channel.with_open_text (sail_module.md.name ^ ".mir.debug") (fun f -> Format.(fprintf (formatter_of_out_channel f)) "%a" IrMir.Pp_mir.ppPrintModule m); m in

  let open Pass.Progression in 
  let active_if cond p = if cond then p else Fun.id in 
  let passes = Fun.id
    @> Hir.transform 
    @> active_if (comp_mode <> Library) ProcessPass.transform
    @> active_if true hir_debug
    @> Thir.transform 
    @> Imports.transform 
    @> MCall.transform 
    @> Mir.transform
    @> active_if false mir_debug
    @> Mono.transform
    @> finish 
  in run passes (return sail_module)
    


let set_target (llm : Llvm.llmodule) (triple:string) : Llvm_target.Target.t * Llvm_target.TargetMachine.t =
  let target = T.Target.by_triple triple in 
  L.set_target_triple triple llm;  let machine = T.TargetMachine.create ~triple target ~reloc_mode:PIC in
  L.set_data_layout (T.TargetMachine.data_layout machine |> T.DataLayout.as_string) llm;
  (target,machine)


let add_opt_passes (pm : [`Module] Llvm.PassManager.t) : unit  = 
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


let link ?(is_lib = false) (llm:Llvm.llmodule) (module_name : string) (basepath:string) (imports: string list) (libs : string list) (target, machine) clang_args : int =
  let f = Filename.(concat basepath module_name ^ Const.object_file_ext) in
  let triple = T.TargetMachine.triple machine in
  let objfiles = String.concat " " (f::imports) in 
  let libs = List.map (fun l -> "-l " ^ l) libs |> String.concat " "  in 
  if T.Target.has_asm_backend target then
    begin
      Logs.info (fun m -> m "emitting object file...");
      T.TargetMachine.emit_to_file llm ObjectFile f machine;
      if not is_lib then 
        begin
        if (Option.is_none (L.lookup_function "main" llm)) then failwith ("no Main process found for module '" ^ module_name ^  "', can't compile as executable");
        let clang_cmd = Fmt.str "clang --target=%s %s -o %s %s %s" triple objfiles module_name libs clang_args in
        Logs.debug (fun m -> m "invoking clang with the following parameters : \n%s" clang_cmd);
        Sys.command clang_cmd
        (* "rm " ^ objfile |>  Sys.command *)
        end
      else 0
    end
  else
    failwith ("target " ^ L.target_triple  llm ^ "doesn't have an asm backend, can't generate object file!")


let execute (llm:L.llmodule) = 
  let module EE = Llvm_executionengine in 
  (* 
    fixme : when depending on other modules, we need to 'Llvm_executionengine.add' them, which implies the .ll must be available to be read.
    This will be revisited when we make use of the .ll files for LTO 
  *)

  let _ = match L.lookup_function "main" llm with
  | Some m -> m
  | None -> failwith "can't execute : no main process found" 
  in
  match EE.initialize () with
  | false -> failwith "unable to start the execution engine"
  | _ -> ();
  let ee = EE.create llm in
  let open Ctypes in 
  let m_t = void @-> returning int in
  let main_addr = EE.get_function_address "main" (static_funptr m_t) ee in 
  let main = coerce (static_funptr m_t) (Foreign.funptr m_t) main_addr in 
  let _ret = main () in 
  EE.dispose ee (* implicitely disposes the module *)


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

let unmarshal_sm file = In_channel.with_open_bin file @@ fun c -> (Marshal.from_channel c : Mono.out_body SailModule.t)
let marshal_sm file m = Out_channel.with_open_bin file @@ fun c -> Marshal.to_channel c m []

let sailor (files: string list) (intermediate:bool) (jit:bool) (noopt:bool) (dump_decl:bool) () (force_comp:bool list) (paths:string list) (comp_mode : Cli.comp_mode)  (clang_args: string) (verify_ir:bool) (target_triple:string) = 
  if Logs.level () = Some Logs.Debug then Printexc.record_backtrace true;

  let compile sail_module basepath (comp_mode : Cli.comp_mode) : unit E.t =
    let* m = apply_passes sail_module comp_mode in    
    let+ llm = C.Codegen_.moduleToIR m dump_decl verify_ir in

    (* only generate mir file if codegen succeeds *)
    marshal_sm Filename.(concat basepath m.md.name ^ Const.mir_file_ext) m;

    let tm = set_target llm target_triple in

    if not noopt && comp_mode <> Library then 
        L.PassManager.(
          let pm = create () in add_opt_passes pm;
          let res = run_module llm pm in
          Logs.debug (fun m -> m "pass manager executed, module modified : %b" res);
          dispose pm
        )
    ;

    if intermediate then L.print_module Filename.(concat basepath m.md.name ^ Const.llvm_ir_ext) llm;

    if not jit then
      begin
        let libs,object_files = List.partition Filename.(fun e -> extension e <> Const.object_file_ext) (FieldSet.elements m.md.libs) in 
        let imports = object_files @ List.map (fun i -> i.dir ^ i.mname ^ Const.object_file_ext) @@ ImportSet.elements m.imports in
        let ret = link llm sail_module.md.name basepath imports libs tm ~is_lib:(comp_mode = Library) clang_args in
        if ret <> 0 then
          Fmt.(str_like stderr "clang couldn't execute properly (error %i)" ret) |> failwith
      end
    ;

    if jit && comp_mode <> Library then execute llm else L.dispose_module llm
  in

  let rec process_file f (treated: string list) (compiling: (string*loc) list) comp_mode : string list E.t = 
    let mname = Filename.(basename f |> remove_extension) in 
    let basepath = Filename.(dirname f) in 

    if List.mem mname treated then
    begin 
      Logs.debug (fun m -> m "skipping module '%s'" mname); 
      return treated
    end
    else
      let treated = mname::treated in 
      let add_imports_decls (curr_env: SailModule.DeclEnv.t ) (imports : ImportSet.t) = 
        ImportSet.fold (fun i -> 
          let file = i.dir ^ i.mname ^ Const.mir_file_ext in 
          Logs.debug (fun m -> m "reading module '%s' from mir file %s" i.mname file); 
          let slmd = unmarshal_sm file in
          (* Logs.debug (fun m -> m "decls of import %s : \n %s" i.mname (SailModule.DeclEnv.string_of_env slmd.declEnv)); *)
          SailModule.DeclEnv.add_import_decls (i, slmd.declEnv)
        )
        imports curr_env 
    in

      let* slmd = Parsing.parse_program f in 
      let process_imports_and_compile () : string list E.t =
        let open MakeOrderedFunctions(ImportCmp) in 
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
            let mir_name = i.mname ^ Const.mir_file_ext in
            let source = i.mname ^ Const.sail_file_ext in
            
            let import = fun m -> {i with dir=Filename.(dirname m ^ dir_sep); proc_order=(List.length compiling)} in 

            match find_file_opt source ~paths:(Filename.current_dir_name::paths),find_file_opt mir_name with
            | Some s,Some m when let mir = unmarshal_sm m in 
                                    Digest.(equal mir.md.hash @@ file s) && 
                                    List.length force_comp < 2 && 
                                    mir.md.version = Const.sailor_version -> (* mir up-to-date with source -> use mir *)
              return (treated,import m)
            | None, Some m -> (* mir but no source -> use mir *)
              let mir = unmarshal_sm m in
              E.throw_if 
              (Error.make dummy_pos @@ Printf.sprintf "module %s was compiled with sailor %s, current is %s" mir.md.name mir.md.version Const.sailor_version)
              (mir.md.version <> Const.sailor_version) 
              >>| fun () -> treated,import m
            | None,None -> (* nothing to work with *)
              E.throw @@ Error.make i.loc "import not found"
            | Some s, _ -> (* source but no mir or mir not up-to-date -> compile *)
              begin
              let+ treated = process_file s treated ((slmd.md.name,i.loc)::compiling) Cli.Library
              in 
              treated,import s
              end 
          ) treated slmd.imports 
        in 
        let declEnv = add_imports_decls slmd.declEnv imports in
        let+ _sm = compile {slmd with imports ; declEnv} basepath comp_mode in
        Logs.info (fun m -> m "======= done processing module '%s' =======\n" slmd.md.name);
        treated
      in

      let mir_file = Filename.(dirname f ^ dir_sep ^ slmd.md.name ^ Const.mir_file_ext) in
      (* if mir file exists, check hash, if same hash, no need to compile *)
      if Sys.file_exists mir_file && (List.length force_comp = 0) then
        let mir = unmarshal_sm mir_file in
        let* () = E.throw_if (Error.make dummy_pos @@ Printf.sprintf "module %s was compiled with sailor %s, current is %s" mir.md.name mir.md.version Const.sailor_version)
                  (mir.md.version <> Const.sailor_version) 
        in
        if not @@ Digest.equal mir.md.hash slmd.md.hash then
          process_imports_and_compile ()
        else 
          begin
            Logs.app (fun m -> m "'%s' is up-to-date, use '-f' to force compilation" slmd.md.name);
            return treated
          end
      else
        process_imports_and_compile () 
      in 

  try
    match ListM.fold_left (fun t f -> let+ t = process_file f t [] comp_mode in f::t) [] files with
    | Ok treated,_ -> Logs.debug (fun m -> m "files processed : %s " @@ String.concat " " treated) ; `Ok ()
    | Error e,errs -> 
      Error.print_errors (e::errs);
      `Error(false, "compilation aborted") 
  with
  | e ->
    let msg = 
      if (Printexc.backtrace_status () |> not) then (
        Logs.info (fun m -> m "backtrace recording is not turned on, only the exception name will be printed. To print the backtrace, run under verbose mode or with 'OCAMLRUNPARAM=b'");
        Printexc.to_string e)
      else Fmt.str "%s \n\n %s" (Printexc.to_string e) (Printexc.get_backtrace ()) in 
    `Error (false,msg)


let () = 
  Llvm_all_backends.initialize ();
  L.enable_pretty_stacktrace ();
  L.install_fatal_error_handler (fun err -> Logs.err (fun m -> m "LLVM ERROR : '%s'\n" err));
  Cmdliner.Cmd.eval (Cli.cmd sailor) |> exit