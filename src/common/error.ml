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



module MonadErrorTransformer (M : Monad)  : MonadTransformer
with type 'a t = ('a, error_type) Result.t M.t and type 'a old_t = 'a M.t  = struct
  open MonadSyntax(M)

  type 'a t = ('a, error_type) Result.t M.t

  type 'a old_t = 'a M.t

  let pure x = Result.ok x |> M.pure

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = let+ x in Result.map f x 

  let ( <*> ) f x = let* f in match f with Ok f -> fmap f x  | Error e -> Error e |> M.pure

  let (>>=) (x: 'a t) (f:('a -> 'b t)) : 'b t = 
    let* x in match x with
    | Ok v -> f v
    | Error e -> Error e |> M.pure

  let (>>|) (x:'a t) (f:('a -> 'b)) : 'b t = x >>= (fun x -> pure (f x))

  let lift x = let+ x in Result.ok x

end


module MonadError = MonadErrorTransformer(MonadIdentity)


