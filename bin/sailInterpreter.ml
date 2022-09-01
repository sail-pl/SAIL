open Cmdliner
open Common
open TypesCommon
open CliCommon
open Evaluator
open SailParser

let saili (files: string list) (intermediate:bool) () = 
  let rec aux = function
  | f::r -> 
    begin
      match Parsing.parse_program f  with
      | fcontent,(Ok(p),errors) ->
        Error.print_errors fcontent errors;

        let signatures =  [SailModule.signatureOfModule p; ExternalsInterfaces.exSig] in 
        let p' = Translator.program_translate signatures p in
        if intermediate then (
          let file_w = f ^ ".intermediate" |> open_out in
          let output = Format.formatter_of_out_channel file_w in 
          Format.fprintf output "%a\n" (PpCommon.pp_program Intermediate.pp_print_method Intermediate.pp_print_command) p'
        );
        let c = List.find_opt (fun n -> String.equal n.p_name "Main") p'.processes in
        begin 
          match c with 
          | None -> failwith "no main process"
          | Some c -> Evaluator_.start p'.methods c.p_body 
        end;
        begin
        match r with 
        | [] -> `Ok ()
        | l ->  aux l
        end;
      | fcontent,(Error e, errlist) -> Common.Error.print_errors fcontent @@ e::errlist; `Error (false, "evaluation aborted")
    end
  | [] -> `Ok ()
  
in try aux files with | e -> `Error (false,Printexc.to_string e)
        

let intermediate_arg = intermediate_arg "generate intermediate code"

let cmd =
  let doc = "SaIL Interpreter" in
  let info = Cmd.info "saili" ~doc in
  Cmd.v info Term.(ret (const saili $ sailfiles_arg $ intermediate_arg $ setup_log_term))

let () = Cmd.eval cmd |> exit