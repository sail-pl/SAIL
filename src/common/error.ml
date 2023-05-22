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
    hint : (TypesCommon.loc option * string) option;
    label : string option;
  } 
  type errors = error list
  type 'a result = ('a, errors) Result.t

  let make ?(why=None) ?(hint=None) ?(label=None) where what : error = 
   {where;what;why;label;hint}
  
   let print_errors (errs:errors) : unit =  
    let print_indication fmt  (where: TypesCommon.loc) what : unit = 
      let location = MenhirLib.LexerUtil.range where in
      let f = ((fst where).pos_fname |> open_in |> In_channel.input_all) in
      let indication = show_context f where in 
      let start = String.make ((fst where).pos_cnum - (fst where).pos_bol )' ' in
      let ending = String.make ((snd where).pos_cnum - (fst where).pos_cnum )'^' in
      Fmt.pf fmt "@[<v>%s@ %s@ %s%s %s@,@]@ @ " location indication start ending what
    in
    if errs <> [] then
    let s fmt = List.iter (
      fun {where;what;hint;_} ->
        if where = (dummy_pos,dummy_pos) then
          Fmt.pf fmt "@[<v>%s@ @] @ @ " what
        else
          print_indication fmt where what;
          match hint with 
          | Some (where,h) -> 
            begin
             match where with
             | Some loc -> print_indication fmt loc h                
             | None -> Fmt.pf fmt "@[<v>Hint : %s @ @]@ " h
            end
          | None -> ()
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

  val get_error : 'a t -> (error -> unit) -> 'a t
  val throw : error -> 'a t
  val log : error -> unit t
  val recover : 'a -> 'a t -> 'a t
  val fail :  'a t -> 'a t
  val log_if : bool -> error -> unit t
  val throw_if : bool -> error -> unit t
  val throw_if_none : 'a option -> error -> 'a t
  val get_warnings : 'a t -> (error list -> unit) -> 'a t


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


  let get_error (x : 'a t) (f:error -> unit) : 'a t = 
    let* v,l = x in 
    match v with
    | Error err -> f err; ((Error err),l) |> M.pure 
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

  let throw_if_none (x:'a option) (e: error) : 'a t = 
    match x with
    | None -> throw e
    | Some r -> (Ok r,[])  |> M.pure

  let get_warnings (x : 'a t) (f : error list -> unit) : 'a t =
    let+ v,l = x in f l; (v,l) 

end

module Logger = MakeTransformer(MonadIdentity)