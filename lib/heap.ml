open MyUtil
 
module type Heap = sig 
  (* the type of addresses *)
  type address

  type elt
  (* the type of heaps *)
  type t
  (* fetch the value at some address *)
  val empty : t
  val fetch : t -> address -> elt option option 
  (* update the value at some address *)
  val update : t -> (address * elt) -> t option 
  (* allocate fresh address *)
  val fresh : t -> address * t
  (* *)
  val free : t -> address -> t option

  val pp_address : Format.formatter -> address -> unit
  val pp_t : Format.formatter -> t -> unit
end


module Heap (Addr : OrderedValue) (Val : Value) : Heap with type elt = Val.t and type address = Addr.t = struct 

  module M  = Map.Make(Addr)

  type address = M.key

  type elt = Val.t

  type t = {
    map : elt option M.t;
    freelist : address list;
    next : address;
  }
  
  let pp_address (f : Format.formatter) (a : address) = Format.fprintf f "%a"  Addr.pp_t a

  let empty = {map = M.empty; freelist=[];next=Addr.bottom}

  let pp_option (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter) (x : 'a option) : unit =
    match x with 
        None -> Format.fprintf pf "_"
      |  Some x -> pp_a pf x

  let pp_t (pf : Format.formatter) (h : t) : unit =
    Format.fprintf pf "{%a}"  
      (Format.pp_print_list (pp_pair Addr.pp_t (pp_option Val.pp_t))) (M.bindings h.map)

  (** [fetch ]*)
  let fetch (h : t) (l : address) : elt option option =
    M.find_opt l h.map
   
  let update (h : t) ((l,v) : address * elt) :  t option =
    Some
      { map = M.update l (fun _ -> Some (Some v)) h.map;
        freelist = h.freelist;
        next = h.next;}
  
  let fresh (h : t) : address *  t =
    match h.freelist with
    | [] ->
      
        ( h.next,
          { map = M.add h.next None h.map;
            freelist = [];
            next = Addr.next h.next;
          } )
    | l :: t -> 
      (l, { map = M.add l None h.map; freelist = t; next = h.next })

  (* let free (h : t) (l : address) : t option = 
    if M.mem l h.map then 
      Some {map = M.remove l h.map; freelist = l::h.freelist; next = h.next} 
    else None *)
  let free (h : t) (_l: address) : t option = Some h
end

