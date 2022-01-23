open MyUtil

module type Env = sig 

  type elt 

  type t  

  type frame
  val empty : t

  val emptyFrame : frame

  val top : t -> (frame * t) option

  val singleton : string -> elt -> frame 
  val record : t -> string * elt -> t option
  val fetchLoc :  t -> string -> elt option

  val activate : t -> frame -> t

  val push : t -> frame -> t option
  val merge : frame -> frame -> frame
  val allValues : frame -> elt list

  val deactivate : t -> (elt list *  t) option

  val concat : t -> t -> t

  val pp_t : Format.formatter -> t  -> unit
end

module Env (V : Value): Env  with type elt = V.t = struct 

  module S = Map.Make (String)

  type elt = V.t 

  type t = elt S.t list

  type frame = elt S.t
  let empty = []
  let emptyFrame = S.empty

  let singleton = S.singleton

  (* let rec varsOf (env : 'a t) : string= 
    match env with 
      [] -> ""
    | fr::env -> 
      "["^(String.concat "," (List.map fst (S.bindings fr)))^"]"^
      (varsOf env) *)

  let pp_pair (pf : Format.formatter) ((x, v) : string * 'a) : unit =
    Format.fprintf pf "(%s:%a)" x V.pp_t v
    
  let pp_frame (pf : Format.formatter) (fr : frame) : unit = 
    Format.fprintf pf "[%a]" (Format.pp_print_list pp_pair) (S.bindings fr)

  let pp_t (pf : Format.formatter) (env : t) : unit =
      Format.fprintf pf "%a" (Format.pp_print_list pp_frame) env 

  let top env = match env with [] -> None | h ::t -> Some (h,t)
  (* [record env (x,a)] : augment env with a mapping from a with x *)
  (* it is undefined if x is already defined in env or if env is empty *)
  let record (env : t) ((x,a) : string * elt)  : t option =
  match env with
    | [] -> None
    | h :: t ->
        if S.exists (fun y _ -> x = y) h then None
        else Some (S.add x a h :: t)

  (** [fetchLoc env x] : returns the memory H.address associated with a variable *)
  (* it returns the value mapped by the first element of env defining x *)
  let fetchLoc (env : t) (x : string) : elt option =
    let rec aux (env : t) =
      match env with
      | [] -> None
      | blockvar :: env -> (
          match S.find_opt x blockvar with None -> aux env | _ as x -> x)
    in aux env

  let allValues (e : frame) : elt list = 
      S.fold (fun _ x y -> x::y) e [] 

  let activate (e : t) (fr : frame) =
    fr :: e 

let merge (fr1 : frame) (fr2 : frame) : frame = 
    S.union (fun _ _ y -> Some y) fr1 fr2

  let push (e : t) (fr : frame) : t option =
    match e with 
      | [] -> None 
      | fr'::e' -> Some (S.union (fun _ _ y -> Some y) fr fr' :: e')

  let deactivate (e :'t) : (elt list *  t) option = 
    match e with 
      [] -> None 
      | h::t -> Some (S.fold (fun _ x y -> x::y) h [], t)

  let concat l1 l2 = l1 @ l2
end
