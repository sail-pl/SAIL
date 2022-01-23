module type Value = sig 
  type t 
  val pp_t : Format.formatter -> t -> unit
end

module type Env = sig 

  type 'a t  
  
  type 'a frame
  val empty : 'a t

  val emptyFrame : 'a frame

  val top : 'a t -> 'a frame option

  val singleton : string -> 'a -> 'a frame 
  val record : 'a t -> string * 'a -> 'a t option
  val fetchLoc : 'a t -> string -> 'a option

  val activate : 'a t -> 'a frame -> 'a t

  val merge : 'a frame -> 'a frame -> 'a frame
  val allValues : 'a frame -> 'a list

  val deactivate : 'a t -> ('a list *  'a t) option

  val concat : 'a t -> 'a t -> 'a t
end

module Env : Env = struct 

  module S = Map.Make (String)

  type 'a t = 'a S.t list

  type 'a frame = 'a S.t
  let empty = [S.empty]
  let emptyFrame = S.empty

  let singleton = S.singleton

  (* let rec varsOf (env : 'a t) : string= 
    match env with 
      [] -> ""
    | fr::env -> 
      "["^(String.concat "," (List.map fst (S.bindings fr)))^"]"^
      (varsOf env) *)

  let pp_pair (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter) ((x, v) : string * 'a) : unit =
    Format.fprintf pf "(%s:%a)" x pp_a v
    
  let pp_frame (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter) (fr : 'a frame) : unit = 
    Format.fprintf pf "[%a]" (Format.pp_print_list (pp_pair pp_a)) (S.bindings fr)

  let pp_env (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter) (env : 'a t) : unit =
      Format.fprintf pf "%a" (Format.pp_print_list (pp_frame pp_a)) env

  let top env = match env with [] -> None | h ::_ -> Some h
  (* [record env (x,a)] : augment env with a mapping from a with x *)
  (* it is undefined if x is already defined in env or if env is empty *)
  let record (env : 'a t) ((x,a) : string * 'a)  : 'a t option =
  match env with
    | [] -> None
    | h :: t ->
        if S.exists (fun y _ -> x = y) h then None
        else Some (S.add x a h :: t)

  let pp_fake (pf : Format.formatter) (_ : 'a) : unit = 
    Format.fprintf pf "V"

  (** [fetchLoc env x] : returns the memory H.address associated with a variable *)
  (* it returns the value mapped by the first element of env defining x *)
  let fetchLoc (env : 'a t) (x : string) : 'a option =
    Logs.debug (fun m -> m "fetch env : %a\n" (pp_env pp_fake) env);
    let rec aux (env : 'a t) =
      match env with
      | [] -> None
      | blockvar :: env -> (
          match S.find_opt x blockvar with None -> aux env | _ as x -> x)
    in aux env

  let allValues (e : 'a frame) : 'a list = 
      S.fold (fun _ x y -> x::y) e [] 

  let activate (e : 'a t) (fr : 'a frame)=
    fr :: e 

  let merge fr1 fr2 = S.union (fun _ _ y -> Some y) fr1 fr2

  let deactivate (e :'a t) : ('a list * 'a t) option = 
    match e with 
      [] -> None 
      | h::t -> Some (S.fold (fun _ x y -> x::y) h [], t)

  let concat l1 l2 = l1 @ l2
end
