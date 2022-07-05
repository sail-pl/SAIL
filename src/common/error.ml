open Monad

module E = MenhirLib.ErrorReports


let show_context text (p1,p2) =
  let open Lexing in
  let p1 = { p1 with pos_cnum=p1.pos_bol}
  and p2 = { p2 with pos_cnum= String.index_from text p2.pos_cnum '\n'}  in
  E.extract text (p1,p2) |> E.sanitize


type error_type = (TypesCommon.loc * string) list

type 'a result = ('a, error_type) Result.t


let print_errors (file:string) (errs:error_type) : unit =  
  let s = List.fold_left (
    fun s (l,msg) ->
      let location = MenhirLib.LexerUtil.range l in
      let indication = show_context file l in 
      let start = String.make ((fst l).pos_cnum - (fst l).pos_bol )' ' in
      let ending = String.make ((snd l).pos_cnum - (fst l).pos_cnum )'~' in
      Printf.sprintf "\n%s\n\t%s\n\t%s%s\n%s\n\n%s" location indication start ending msg s
  )
  String.empty errs in
  Logs.err (fun m -> m "found %i error(s) : \n%s" (List.length errs) s)


let partition_result f l  : 'a list * error_type  = 
  let r,e = List.partition_map ( fun r -> match f r with Ok a -> Either.left a | Error e -> Either.right e) l 
  in r,List.flatten e


module MonadError : Monad with type 'a t = 'a result = struct
  type 'a t = ('a, error_type) Result.t

  let fmap = Result.map

  let pure x = Result.ok x

  let ( <*> ) f x = match f with Ok f -> fmap f x | Error e -> Error e

  let ( >>= ) = Result.bind

  let ( >>| ) x f = x >>= fun x -> f x |> pure
end
