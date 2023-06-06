open Cmdliner

module C = Common.Constants

let setup_log style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ())

let setup_log_term =
Term.(const setup_log $ Fmt_cli.style_renderer () $ Logs_cli.level ())


let intermediate_arg doc =
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