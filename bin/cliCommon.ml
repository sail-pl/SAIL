open Parser
open Lexer
open Lexing
open Cmdliner

let print_error_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  Fmt.str "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


let parse_program lexbuf =
  try
    Ok (Parser_.sailModule read_token lexbuf)
  with
  | SyntaxError msg ->
    let error_msg = Fmt.str "%s: %s@." (print_error_position lexbuf) msg in
    Error error_msg
  | Parser_.Error ->
    let error_msg = Fmt.str "%s: syntax error @."
        (print_error_position lexbuf) in
    Error error_msg


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
          let msg = Format.sprintf  "'%s' is not a sail file. Hint: use the .sl extension\n%!" filename in
          Error (`Msg msg)
      else
        let msg = Format.sprintf "'%s' : no such file" filename in
        Error (`Msg msg )
    in
    let print f s = Format.fprintf f "%s" s in
    Arg.conv (parse,print)



let sailfiles_arg = Arg.(non_empty & pos_all sailfile_conv [] & info [])