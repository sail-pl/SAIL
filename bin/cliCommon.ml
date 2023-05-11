open Cmdliner

let prefix = "libr--"
let prefix_size = String.length prefix

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
        if String.equal (Filename.extension filename) ".sl" then 
          (Ok filename)
        else 
          let msg = Fmt.str "'%s' is not a sail file. Hint: use the .sl extension\n%!" filename in
          Error (`Msg msg)
      else
      	if (String.starts_with ~prefix filename) then
      		(Ok filename)
      	else
        	let msg = Fmt.str "'%s' : No such file" filename in
        	Error (`Msg msg )
    in
    let print f s = Format.fprintf f "%s" s in
    Arg.conv (parse,print)



let sailfiles_arg = Arg.(non_empty & pos_all sailfile_conv [] & info [])
