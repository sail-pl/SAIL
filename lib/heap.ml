(* open MyUtil *)
 
module type Heap = sig 
  (* the type of addresses *)
  type address
  (* the type of heaps *)
  type 'a t
  (* fetch the value at some address *)
  val empty : 'a t
  val fetch : 'a t -> address -> 'a option option 
  (* update the value at some address *)
  val update : 'a t -> (address * 'a) -> 'a t option 
  (* allocate fresh address *)
  val fresh : 'a t -> address * 'a t
  (* *)
  val free : 'a t -> address -> 'a t option

  val pp_address : Format.formatter -> address -> unit
end


module Heap : Heap  = struct 

  module M  = Map.Make(Int64)

  type address = M.key
  
  let pp_address (f : Format.formatter) (a : address) = Format.fprintf f "%d"  (Int64.to_int a)

  type 'a t = {
    map : 'a option M.t;
    freelist : address list;
    next : address;
  }

  let empty = {map = M.empty; freelist=[];next=0L}

  (** [fetch ]*)
  let fetch (h : 'a t) (l : address) : 'a option option =
    Logs.debug (fun m -> m "fetch address %a \n"  pp_address l);
    M.iter (fun a _ -> Logs.debug (fun m -> m "%a" pp_address a )) h.map;
    M.find_opt l h.map
   
  let update (h : 'a t) ((l,v) : address * 'a) : 'a t option =
    Some
      { map = M.update l (fun _ -> Some (Some v)) h.map;
        freelist = h.freelist;
        next = h.next;}
  
  let fresh (h : 'a t) : address * 'a t =
    match h.freelist with
    | [] ->
        ( Int64.add h.next 1L,
          { map = M.add h.next None h.map;
            freelist = [];
            next = Int64.add h.next 1L;
          } )
    | l :: t -> (l, { map = M.add l None h.map; freelist = t; next = h.next })

  let free (h : 'a t) (l : address) : 'a t option = 
    if M.mem l h.map then 
      Some {map = M.remove l h.map; freelist = l::h.freelist; next = h.next} 
    else None
end

