open Cmdliner

module C = Common.Constants

let setup_log style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ())

let setup_log_term =
Term.(const setup_log $ Fmt_cli.style_renderer () $ Logs_cli.level ())


let intermediate_arg =
  let doc =  "save the LLVM IR" in
  let info = Arg.info ["i"; "intermediate"] ~doc in
  Arg.flag info |> Arg.value


let sailfile_conv =
  let parse filename =
      if Sys.file_exists filename && not (Sys.is_directory filename) then
        if String.equal (Filename.extension filename) C.sail_file_ext then 
          (Ok filename)
        else 
          let msg = Fmt.str "'%s' is not a sail file. Hint: use the '%s' extension\n%!" filename C.sail_file_ext in
          Error (`Msg msg)
      else
        let msg = Fmt.str "'%s' : no such file" filename in
        Error (`Msg msg )
    in
    let print f s = Format.fprintf f "%s" s in
    Arg.conv (parse,print)



let sailfiles_arg = Arg.(non_empty & pos_all sailfile_conv [] & info [])

type comp_mode = Library | Executable


let jit_arg =
  let doc = "execute using the LLVM JIT compiler" in 
   Arg.(value & flag & info ["run"] ~doc)


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

let verify_ir =
  let doc = "assert generated LLVM IR is correct" in 
  let i = Arg.info ["verify_ir"] ~doc in
  Arg.(value & opt bool true i)
  
let mode_arg = 
  let doc = "How to compile the current file : $(b,lib) to only generate the object file, $(b,exe) for an executable." in
  let mode = Arg.enum ["lib", Library; "exe", Executable] in
  Arg.(value & opt mode Executable & info ["m"; "mode"] ~doc)

let clang_args = 
  let doc = "extra args to pass to clang" in 
  Arg.(value & opt string ""  & info  ["clang-args"] ~doc)


let target_triple = 
  let open Llvm_target in
  let target_conv = 
  let print f s = Format.fprintf f "%s" s in
  let parse triple = 
    try 
      Target.by_triple triple |> ignore;
      Ok triple
    with Error e -> Error (`Msg e)
  in
  Arg.conv (parse,print)
in
let doc = "choose for what target to compile, defaults to the system target" in 
Arg.(value & opt target_conv (Target.default_triple ()) & info  ["target"] ~doc)
        
      
let cmd = fun pgrm ->
  let doc = "SaiLOR, the SaIL cOmpileR" in
  let info = Cmd.info "sailor" ~doc ~version:C.sailor_version in
  Cmd.v info Term.(ret (const pgrm $ sailfiles_arg $ intermediate_arg $ jit_arg $ noopt_arg $ dump_decl_arg $ setup_log_term $ force_comp $ extra_paths $ mode_arg $ clang_args $ verify_ir $ target_triple))
    

