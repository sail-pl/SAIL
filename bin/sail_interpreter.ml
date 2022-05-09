open Core
open Sail_common

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
                let p = p (Filename.chop_extension (Filename.basename filename)) in
                let signatures =  [Common.signatureOfModule p; ExternalsInterfaces.exSig] in 
                  let p' = Translator.program_translate signatures p in
                   let _ = 
                    if intermediate then 
                      Out_channel.with_file ("sail.intermediate") ~f:(fun y -> 
                        let output = Format.formatter_of_out_channel y in
                        Format.fprintf output "%a\n" (Pp_common.pp_program Intermediate.pp_print_command) p'                         
                      ) in 
                  let c = List.find p'.processes ~f:(fun x -> String.equal x.p_name "Main") in
                    begin match c with 
                      None -> failwith "no main process "
                    | Some c -> 
                      let _ = Evaluator.start p'.methods c.p_body in ()
               end
               | Error(e) -> Error.raise e
             )
    )

let _ = 
  command |> Command_unix.run ~version:"0.1"