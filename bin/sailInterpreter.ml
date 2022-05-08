open Cmdliner
open Common
open CliCommon

let saili (files: string list) (intermediate:bool) (l : Logs.level option)  = 
  Logs.set_level l;
  Logs.set_reporter (Logs_fmt.reporter ());

  let rec aux = function
  | f::r -> 
    let file_r = open_in f in
    let lexbuf = Lexing.from_channel file_r in
    begin
      match parse_program lexbuf with
      | Ok(p) ->
        let p = p (Filename.chop_extension (Filename.basename f)) in
        let signatures =  [Common.signatureOfModule p; ExternalsInterfaces.exSig] in 
        let p' = Translator.program_translate signatures p in
        if intermediate then (
          let file_w = f ^ ".intermediate" |> open_out in
          let output = Format.formatter_of_out_channel file_w in
          Format.fprintf output "%a\n" (Pp_common.pp_program Intermediate.pp_print_command) p'
        );
        let c = List.find_opt (fun n -> String.equal n.p_name "Main") p'.processes in
        begin 
          match c with 
          | None -> failwith "no main process"
          | Some c -> Evaluator.start p'.methods c.p_body 
        end;
        begin
        match r with 
        | [] -> `Ok ()
        | l ->  aux l
        end;
      | Error(e) ->`Error (false, e)
    end
  | [] -> `Ok ()
  
in aux files
        

let intermediate_arg = intermediate_arg "generate intermediate code"

let cmd =
  let doc = "SaIL Interpreter" in
  let info = Cmd.info "saili" ~doc in
  Cmd.v info Term.(ret (const saili $ sailfiles_arg $ intermediate_arg $ verbose_arg))

let () = Cmd.eval cmd |> exit