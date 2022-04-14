open Core
open Sail_common
let parse_AST = fun _ -> ()

let command = 
  Command.basic ~summary:"sail compiler" 
    Command.Let_syntax.( 
      let%map_open filename = Command.Param.(anon ("input files" %: sailfile_type))
      and verbose = verbose_param
      in fun () -> 
        Logs.set_level verbose;
        Logs.set_reporter (Logs_fmt.reporter ());
        In_channel.with_file filename
           ~f:(fun x ->
               let lexbuf = Lexing.from_channel x in
               match parse_program lexbuf with
               | Ok(p) -> parse_AST p
               | Error(e) -> Error.raise e
             )
    )

let main = 
  command |> Command_unix.run ~version:"0.1"