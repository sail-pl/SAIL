open Lexing
open Monad

let show_context text (p1,p2) =
  let open MenhirLib.ErrorReports in
  let p1 = { p1 with pos_cnum=p1.pos_bol} 
  and p2 = match String.index_from_opt text p2.pos_cnum '\n' with
  | Some pos_cnum ->  { p2 with pos_cnum } 
  | None -> p2
  in
  extract text (p1,p2) |> sanitize


  type error = 
  {
    where : TypesCommon.loc;
    what :   string;
    why : (TypesCommon.loc option * string) option;
    hint : string option;
    label : string option;
  } 
  type errors = error list
  type 'a result = ('a, errors) Result.t

  let make ?(why=None) ?(hint="") ?(label="") where what : error = 
    let option_of_string = function "" -> None | s -> Some s in 
    let label = option_of_string label 
    and hint = option_of_string hint in
   {where;what;why;label;hint}
  
   let print_errors (file:string) (errs:errors) : unit =  
    if errs <> [] then
    let s fmt = List.iter (
      fun {where;what;hint;_} ->
        if where = (dummy_pos,dummy_pos) then
          Logs.debug (fun m -> m "found one error at an unknown location : \n\t %s \n" what)
        else
          let location = MenhirLib.LexerUtil.range where in
          let indication = show_context file where in 
          let start = String.make ((fst where).pos_cnum - (fst where).pos_bol )' ' in
          let ending = String.make ((snd where).pos_cnum - (fst where).pos_cnum )'^' in
          Fmt.pf fmt "@[<v>%s@ %s@ %s%s %s@,@]@ @ " location indication start ending what;
          Format.pp_print_option  (fun fmt -> Fmt.pf fmt "@[<v>Hint : %s @ @]@ ") fmt hint
      )
     errs in
     Logs.err (fun m -> m "@[<v 5>found %i error(s) :@." (List.length errs) );
     s Fmt.stderr


(* taken from http://rosettacode.org/wiki/Levenshtein_distance#A_recursive_functional_version *)
let levenshtein_distance s t =
  let m = String.length s
  and n = String.length t in
  let d = Array.make_matrix (m + 1) (n + 1) 0 in
  for i = 0 to m do d.(i).(0) <- i done;
  for j = 0 to n do  d.(0).(j) <- j done;
  for j = 1 to n do
    for i = 1 to m do
      if s.[i - 1] = t.[j - 1] then d.(i).(j) <- d.(i - 1).(j - 1)
      else
        d.(i).(j) <- min (d.(i - 1).(j) + 1) (min (d.(i).(j - 1) + 1) (d.(i - 1).(j - 1) + 1))
    done
  done;
  d.(m).(n)
  


module type Logger = sig
  include MonadTransformer
  val catch : 'a t -> (error -> 'a t) -> 'a t
  val throw : error -> 'a t
  val log : error -> unit t
  val recover : 'a -> 'a t -> 'a t
  val fail :  'a t -> 'a t
  val log_if : bool -> error -> unit t
  val throw_if : bool -> error -> unit t

end

 module MakeTransformer (M : Monad) : Logger with type 'a t = (('a,error) Result.t * error list) M.t and type 'a old_t = 'a M.t = struct 
  open MonadSyntax(M)

  type 'a old_t = 'a M.t
  type 'a t = (('a, error) Result.t * error list) old_t

  let pure (x:'a) : 'a t = (Ok x,[]) |> M.pure

  let fmap (f: 'a -> 'b) (x:'a t) : 'b t =
    let+ v,l = x in
    match v with
    | Ok x -> Ok (f x),l
    | Error e -> Error e,l

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
  let+ f,l1 = f and* x,l2 = x in
  match f,x with
  | Error err1,Error err2 -> Error err1, err2 :: l1 @ l2 
  | Error err1,_ -> Error err1, l1@l2
  | Ok f, Ok x -> Ok (f x),l1@l2
  | Ok _, Error err ->  Error err,l1@l2

  let bind (x:'a t) (f : 'a -> 'b t) : 'b t = 
  let* v,l1 = x in 
  match v with
  | Error err -> (Error err,l1) |> M.pure
  | Ok x -> let+ v,l2 = f x in v,l1@l2

  let lift (x:'a M.t) : 'a t = let+ x in Ok x,[]

  let throw (e:error) : 'a t = (Error e,[]) |> M.pure

  let catch (x : 'a t) (f:error -> 'a t) : 'a t = 
  let* v,l = x in 
  match v with
  | Error err -> let+ x,l2 = f err in x,l@l2
  | Ok x ->  (Ok x,l) |> M.pure 


  let log (msg:error) : unit t = (Ok (),[msg]) |> M.pure

  let recover (default : 'a)  (x:'a t) : 'a t =
    let+ v,l = x in
      match v with
    | Ok x -> Ok x,l
    | Error err -> Ok default,err::l


  let fail (x:'a t) : 'a t = 
    let+ v,l = x in
    match v,l with
    | Error err,_ -> Error err,l
    | Ok x,[] -> Ok x,[]
    | Ok _,h::t -> Error h,t

  let log_if b e = if b then log e else pure ()
  let throw_if b e = if b then throw e else pure ()


end

module Logger = MakeTransformer(MonadIdentity)