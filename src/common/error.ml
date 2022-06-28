open Monad

type error_type = (TypesCommon.loc * string) list

type 'a result = ('a, error_type) Result.t


let print_errors (errs:error_type) : unit =  
  let open Lexing in
  List.iter (
    fun (l,s) ->
      let ln = l.pos_lnum
      and offset = l.pos_cnum - l.pos_bol in
      Logs.err (fun m -> m "Line %i Column %i : %s "  ln offset s)
  )
  errs


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
