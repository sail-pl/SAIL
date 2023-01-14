(*  based on https://gitlab.inria.fr/fpottier/menhir/-/blob/master/demos/calc-syntax-errors/calc.ml *)

open Common
open Lexer
open Lexing
open Error
module L = MenhirLib.LexerUtil
module E = MenhirLib.ErrorReports


let print_error_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


(* -------------------------------------------------------------------------- *)

(* This part concerns the code-based parser [Parser]. *)



let fastParse filename : (string * AstParser.statement SailModule.t, string) Result.t =
  let text, lexbuf = L.read filename in
  match Parser.sailModule read_token lexbuf with
  | v -> Result.ok (text,(v filename))

  | exception SyntaxError (loc,msg) ->
      let lexer_prefix = "Lexer - " in
      (* removes lexer prefix in case of a lexing error *)
      let msg = String.(if starts_with ~prefix:lexer_prefix msg then sub msg (length lexer_prefix) (length msg - length lexer_prefix) else msg) in
      Error.print_errors text @@ [Error.make loc msg];
      exit 1

  | exception Parser.Error ->
      Result.error text
      


(* -------------------------------------------------------------------------- *)

(* This part concerns the table-based parser [UnitActionsParser]. *)


module I = UnitActionsParser.MenhirInterpreter


 let env = function I.HandlingError env -> env | _ -> assert false

 let state checkpoint : int =
  match I.top (env checkpoint) with
  | Some (I.Element (s, _, _, _)) -> I.number s
  | None -> 0


let get text checkpoint i =
  match I.get i (env checkpoint) with
  | Some (I.Element (_, _, pos1, pos2)) ->
      Error.show_context text (pos1, pos2)
  | None -> "???"
  



let fail text buffer (checkpoint : _ I.checkpoint) =
  let location = E.last buffer 
  and state_num = state checkpoint in
  try
  let message = ParserMessages.message state_num in
  let message = E.expand (get text checkpoint) message in
  Logs.debug (fun m -> m "reached error state %i "state_num);
  Logger.throw @@ Error.make location message
  with Not_found -> 
    Logger.throw @@ Error.make location "Syntax error"
  
  
let slowParse filename text = 
 let lexbuf = L.init filename (Lexing.from_string text) in
 let supplier = I.lexer_lexbuf_to_supplier read_token lexbuf in
 let buffer, supplier = E.wrap_supplier supplier in
 let checkpoint = UnitActionsParser.Incremental.sailModule lexbuf.lex_curr_p in
 I.loop_handle (fun _ -> assert false) (fail text buffer) supplier checkpoint



let parse_program filename : string * AstParser.statement SailModule.t Logger.t = 
  let open Monad.MonadOperator(Logger) in
  match fastParse filename with
  | Result.Ok (txt,sm) -> txt,Logger.pure sm
  | Result.Error txt -> txt,slowParse filename txt

  
  