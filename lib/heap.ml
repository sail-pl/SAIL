(**************************************************************************)
(*                                                                        *)
(*                                 SAIL                                   *)
(*                                                                        *)
(*             Frédéric Dabrowski, LMV, Orléans University                *)
(*                                                                        *)
(* Copyright (C) 2022 Frédéric Dabrowski                                  *)
(*                                                                        *)
(* This program is free software: you can redistribute it and/or modify   *)
(* it under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or      *)
(* (at your option) any later version.                                    *)
(*                                                                        *)
(* This program is distributed in the hope that it will be useful,        *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of         *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          *)
(* GNU General Public License for more details.                           *)
(*                                                                        *)
(* You should have received a copy of the GNU General Public License      *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>. *)
(**************************************************************************)

open Pp_util
 
module type Heap = sig 
  (* the type of addresses *)
  type address
  (* the type of heaps *)
  type 'a t
  (* fetch the value at some address *)
  val empty : 'a t
  val getLocation : 'a t -> address -> 'a option option 
  (* update the value at some address *)
  val update : 'a t -> (address * 'a ) -> 'a t option 
  (* allocate fresh address *)
  val fresh : 'a t -> address * 'a t
  (* *)
  val free : 'a t -> address -> 'a t option

  val pp_address : Format.formatter -> address -> unit 
  val pp_t : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module Heap  : Heap = struct 

  module M  = Map.Make(Int64)

  type address = M.key

  type 'a t = {
    map : 'a option M.t;
    freelist : address list;
    next : address;
  }
  let pp_address pf a =  Format.fprintf pf "%Ld" a
  
  let empty = {map = M.empty; freelist=[];next=Int64.zero}

  let pp_t (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter) (h : 'a t) : unit =
    Format.fprintf pf "{%a}"  
      (Format.pp_print_list (pp_print_pair pp_address (pp_print_option pp_a))) (M.bindings h.map)

  let getLocation (h : 'a t) (l : address) : 'a option option =
    M.find_opt l h.map
   
  let update (h : 'a t) ((l,v) : address * 'a) :  'a t option =
    Some
      { map = M.update l (fun _ -> Some (Some v)) h.map;
        freelist = h.freelist;
        next = h.next;}
  
  let fresh (h : 'a t) : address *  'a t =
    match h.freelist with
    | [] ->
        ( h.next,
          { map = M.add h.next None h.map;
            freelist = [];
            next = Int64.succ h.next;
          } )
    | l :: t -> 
      (l, { map = M.add l None h.map; freelist = t; next = h.next })

  (* let free (h : t) (l : address) : t option = 
    if M.mem l h.map then 
      Some {map = M.remove l h.map; freelist = l::h.freelist; next = h.next} 
    else None *)
  let free (h : 'a t) (_l: address) : 'a t option = 
    Logs.warn (fun m-> m "Free not implemented yet");Some h
end

