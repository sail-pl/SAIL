let pure o = 
  Some o
let apply f o = 
  match (f, o) with 
    Some f, Some o -> Some (f o)
    | _ -> None 

let ( <*> ) fa xa = apply fa xa

let bind o f =
  match o with
  | Some x  -> f x
  | None    -> None

let join x = 
  match x with 
    None -> None 
  | Some x -> x

let ( >>= ) o f = bind o f

let ( let* ) = bind

let return x = Some x 

let (and*) x y = 
  match (x,y) with 
    (Some x, Some y) -> Some (x,y)
    | _ -> None 

let map1 f (x,y) = (f x, y)
let map2 f (x, y) = (x ,f y)
    
    
let rec optionlist (l : 'a option list) : 'a list option =
  match l with 
  [] -> Some []
  | None :: _ -> None
  | (Some x)::l -> 
      match optionlist l with None -> None | Some t -> (Some (x::t))
    

let flip f = fun x y -> f y x

type ('a, 'b) sum = Inl of 'a | Inr of 'b


let rec fold_leftM (f : 'a -> 'b -> 'a option) (x : 'a) (l : 'b list ) : 'a option =
  match l with 
    | [] -> Some x 
    | h::t -> fold_leftM f x t >>= (flip f) h

    let curry f x y = f (x,y)
let uncurry f x = f (fst x) (snd x)


let rec listMapM (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  match l with 
    [] -> Some []
  | h :: t -> 
      let* h' = f h in 
      let* t'= listMapM f t in 
      Some (h' :: t')

      let inl (v : ('a, 'b) sum) : 'a option =
        match v with Inl x -> Some x | _ -> None
      
      let inr (v : ('a, 'b) sum) : 'b option =
        match v with Inr x -> Some x | _ -> None
      
module type Value = sig 
  type t 
  val pp_t : Format.formatter -> t -> unit
end

module type OrderedValue = sig 
  include Map.OrderedType 
  val pp_t : Format.formatter -> t -> unit
  val bottom : t
  val next : t -> t
end


let pp_pair (pp_a : Format.formatter -> 'a -> unit) (pp_b : Format.formatter -> 'b -> unit)
            (pf : Format.formatter) ((x, v) : 'a * 'b) : unit =
  Format.fprintf pf "(%a:%a)" pp_a x pp_b v