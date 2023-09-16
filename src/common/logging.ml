open Lexing
open Monad

type msg = 
{
  where : TypesCommon.loc;
  what :  string;
  why : (TypesCommon.loc option * string) option;
  hint : (TypesCommon.loc option * string) option;
  label : string option;
} 

let make_msg ?(why=None) ?(hint=None) ?(label=None) where what : msg = {where;what;why;label;hint;}


type log = {errors: msg list; warnings : msg list}

module Log : Monoid with type t = log = struct
  type t = log
  let mempty = {errors=[]; warnings=[]}
  let mconcat l1 l2 = {errors=l1.errors@l2.errors;warnings=l1.warnings@l2.warnings} 
end


let show_context text (p1,p2) =
  let open MenhirLib.ErrorReports in
  let p1 = { p1 with pos_cnum=p1.pos_bol} 
  and p2 = match String.index_from_opt text p2.pos_cnum '\n' with
  | Some pos_cnum ->  { p2 with pos_cnum } 
  | None -> p2
  in
  extract text (p1,p2) |> sanitize



  
let print_log (log:Log.t) : unit =  
  let print_indication fmt  (where: TypesCommon.loc) what : unit = 
    let location = MenhirLib.LexerUtil.range where in
    let f = ((fst where).pos_fname |> open_in |> In_channel.input_all) in
    let indication = show_context f where in 
    let start = String.make ((fst where).pos_cnum - (fst where).pos_bol )' ' in
    let ending = String.make ((snd where).pos_cnum - (fst where).pos_cnum )'^' in
    Fmt.pf fmt "@[<v>%s@ %s@ %s%s %s@,@]@ @ " location indication start ending what
  in
  
  let format_msg fmt msg = 
    if msg.where = (dummy_pos,dummy_pos) then
      Fmt.pf fmt "@[<v>%s@ @] @ @ " msg.what
    else
      print_indication fmt msg.where msg.what;
      match msg.hint with 
      | Some (where,h) -> 
        begin
          match where with
          | Some loc -> print_indication fmt loc h                
          | None -> Fmt.pf fmt "@[<v>Hint : %s @ @]@ " h
        end
      | None -> ()
    
  in
    (* Logs.err (fun m -> m "@[<v 5>found %i error(s) :@." (List.length errs) ); *)

  List.iter (format_msg Fmt.stderr) log.errors;
  List.iter (format_msg Fmt.stderr) log.warnings


    

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
  val catch :  (msg -> 'a t) -> 'a t -> 'a t

  val get_error : (msg -> unit) -> 'a t -> 'a t
  val throw : msg -> 'a t
  val log : msg -> unit t
  val recover : 'a -> 'a t -> 'a t
  val fail :  'a t -> 'a t
  val log_if : msg -> bool ->  unit t
  val throw_if : msg -> bool ->  unit t
  val throw_if_none : msg -> 'a option -> 'a t
  val throw_if_some :  ('a -> msg) -> 'a option -> unit t

  val get_warnings : (msg list -> unit) -> 'a t -> 'a t

  val run : ('a -> 'b t) -> ('b -> unit) -> (msg list -> unit) -> 'a -> unit old_t


end

 module MakeTransformer (M : Monad) (*: Logger with type 'a t = (('a,msg) Result.t * msg list) M.t and type 'a old_t = 'a M.t *) = struct 
  open MonadSyntax(M)

  type 'a old_t = 'a M.t
  type 'a t = (('a, msg) Result.t * log) old_t

  let pure (x:'a) : 'a t = (Ok x,Log.mempty) |> M.pure

  let fmap (f: 'a -> 'b) (x:'a t) : 'b t =
    let+ v,l = x in
    match v with
    | Ok x -> Ok (f x),l
    | Error e -> Error e,l

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    let+ f,l1 = f and* x,l2 = x in
    match f,x with
    | Error err1 , Error err2 -> Error err1, Log.mconcat l1 {l2 with errors=err2::l2.errors}
    | Error err1,_ -> Error err1, Log.mconcat l1 l2
    | Ok f, Ok x -> Ok (f x),Log.mconcat l1 l2
    | Ok _, Error err ->  Error err,Log.mconcat l1 l2

  let bind (x:'a t) (f : 'a -> 'b t) : 'b t = 
    let* v,l1 = x in 
    match v with
    | Error err -> (Error err,l1) |> M.pure
    | Ok x -> let+ v,l2 = f x in v,Log.mconcat l1 l2

  let lift (x:'a M.t) : 'a t = let+ x in Ok x,Log.mempty

  let throw (e:msg) : 'a t = (Error e,Log.mempty) |> M.pure

  let catch (f:msg -> 'a t) (x : 'a t) : 'a t = 
    let* v,l = x in 
    match v with
    | Error err -> let+ x,l2 = f err in x,Log.mconcat l l2
    | Ok x ->  (Ok x,l) |> M.pure 


  let get_error  (f:msg -> unit) (x : 'a t) : 'a t = 
    let* v,l = x in 
    match v with
    | Error err -> f err; ((Error err),l) |> M.pure 
    | Ok x ->  (Ok x,l) |> M.pure 
  

  let log (msg:msg) : unit t = (Ok (),{errors=[]; warnings=[msg]}) |> M.pure

  let recover (default : 'a)  (x:'a t) : 'a t =
    let+ v,l = x in
      match v with
    | Ok x -> Ok x,l
    | Error err -> Ok default,{l with errors=err::l.errors}


  let fail (x:'a t) : 'a t = 
    let+ v,l = x in
    match v,l with
    | Error err,_ -> Error err,l
    | Ok x,{errors=[];_} -> Ok x,l
    | Ok _,{errors=h::t;_} -> Error h,{l with errors=t}

  let log_if e b = if b then log e else pure ()
  let throw_if e b = if b then throw e else pure ()

  let throw_if_none  (e: msg) (x:'a option) : 'a t = 
    match x with
    | None -> throw e
    | Some r -> pure r

  let throw_if_some  (f: 'a -> msg) (x:'a option) : unit t = 
    match x with
    | Some r -> throw (f r)
    | None -> pure ()


  let get_warnings  (f : msg list -> unit) (x : 'a t) : 'a t =
    let+ v,l = x in f l.warnings; (v,l) 

  let run (f : 'a -> 'b t) (on_success : 'b -> unit) (on_error : log -> unit) : 'a -> unit old_t = 
    fun x -> let* res = f x in
    match res with
    | Error e,l -> return (on_error {l with errors=e::l.errors})
    | Ok x,_ -> return @@ on_success x
end

module Logger = MakeTransformer(MonadIdentity)