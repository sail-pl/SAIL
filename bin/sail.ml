open Core
open Lexer
open Lexing
open Evaluator 

let _ = reduce
let print_error_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  Fmt.str "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_program lexbuf =
  try
    Ok (Parser.program Lexer.read_token lexbuf)
  with
  | SyntaxError msg ->
    let error_msg = Fmt.str "%s: %s@." (print_error_position lexbuf) msg in
    Error (Error.of_string error_msg)
  | Parser.Error ->
    let error_msg = Fmt.str "%s: syntax error @."
        (print_error_position lexbuf) in
    Error (Error.of_string error_msg)

let get_file_extension (filename : string) : string =
  String.split_on_chars filename ~on:['.'] |> List.last |> Option.value ~default:""

let sailfile_type =
  let error_not_file filename =
    Format.printf  "'%s' is not a sail file. Hint: use the .sl extension\n%!" filename ;
    exit 1 in
  Command.Spec.Arg_type.create (fun filename ->
      match Sys.is_file filename with
      | `Yes ->
          if String.equal (get_file_extension filename) "sl" then filename
          else error_not_file filename
      | `No | `Unknown -> Format.printf  "'%s' No such file\n%!" filename ;
              exit 1
      )

let verbose_type =
  let error_not_level level = 
    Format.printf "'%s' is not a debug level. Hint use 'app' 'error' 'warning' 'info' or 'debug'" level; exit 1 in
  Command.Spec.Arg_type.create (fun level ->
    match Logs.level_of_string level with 
        Ok (Some l) -> l 
      | _ -> error_not_level level 
  )

let verbose_param =
  let open Command.Param in
  flag "-verbose" (optional verbose_type) 
    ~doc:"set verbose level : 'app' 'error' 'warning' 'info' or 'debug'"


let command = 
  Command.basic ~summary:"sail interpreter" 
    Command.Let_syntax.( 
      let%map_open filename = Command.Param.(anon ("input files" %: sailfile_type))
      and verbose = verbose_param
      and intermediate = flag "-intermediate" no_arg ~doc:"generate intermediate code"
      in fun () -> 
        Logs.set_level verbose;
        Logs.set_reporter (Logs_fmt.reporter ());
        In_channel.with_file filename
           ~f:(fun x ->
               let lexbuf = Lexing.from_channel x in
               match parse_program lexbuf with
               | Ok(p) -> 
                  let p' = Translator.program_translate p in
                   let _ = 
                    if intermediate then 
                      Out_channel.with_file ("sail.intermediate") ~f:(fun y -> 
                        let output = Format.formatter_of_out_channel y in
                        Format.fprintf output "%a\n" (Common.pp_program Pp_evaluator.pp_print_command) p'                        
                      ) in 
                  let c = List.find p'.processes ~f:(fun x -> String.equal x.p_name "Main") in
                    begin match c with 
                      None -> failwith "no main process "
                    | Some c -> let _ = Evaluator.start p'.methods c.p_body in ()
               end
               | Error(e) -> Error.raise e
             )
    )

let main = 
  command |> Command.run ~version:"0.1"

(* let _ = evaluator_test () *)
