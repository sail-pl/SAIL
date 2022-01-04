open Core
(* open Command.Param *)
open Lexer
open Lexing

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


let real_file =
  let error_not_file filename =
    eprintf "'%s' is not a sl file. Hint: use the .sl extension\n%!" filename ;
    exit 1 in
  Command.Spec.Arg_type.create (fun filename ->
      match Sys.is_file filename with
      | `Yes ->
          if String.equal (get_file_extension filename) "sl" then filename
          else error_not_file filename
      | `No | `Unknown -> error_not_file filename)

let compile_program _ _ = ()
                          
let command =
  Command.basic ~summary:"real compiler" ~readme:(fun () -> "List options")
    Command.Let_syntax.(
      let%map_open print_ast =
        flag "-print-ast" no_arg ~doc:"Pretty print the parsed AST of the program"     
      and filename = anon (maybe_with_default "-" ("filename" %: real_file)) in
      fun () ->
         In_channel.with_file filename
           ~f:(fun x ->
               let lexbuf = Lexing.from_channel x in
               match parse_program lexbuf with
               | Ok(p) -> compile_program print_ast p
               | Error(e) -> Error.raise e
             )
    )

let main = command |> Command.run ~version:"0.1"
