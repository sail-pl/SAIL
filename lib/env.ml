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

module type Env = sig 

  type 'a t  

  type 'a frame

  val empty : 'a t

  val emptyFrame : 'a frame

  val top : 'a t -> ('a frame * 'a t) option

  val singleton : string -> 'a -> 'a frame 
  val record : 'a t -> string * 'a -> 'a t option
  val getVariable :  'a t -> string -> 'a option

  val activate : 'a t -> 'a frame -> 'a t

  val push : 'a t -> 'a frame -> 'a t option
  val merge : 'a frame -> 'a frame -> 'a frame
  val allValues : 'a frame -> 'a list

  val deactivate : 'a t -> ('a list *  'a t) option

  val concat : 'a t -> 'a t -> 'a t

  val pp_t : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t  -> unit
end

module Env : Env = struct 

  module S = Map.Make (String)

  type 'a t = 'a S.t list

  type 'a frame = 'a S.t
  let empty = []
  let emptyFrame = S.empty

  let singleton = S.singleton

  (* let rec varsOf (env : 'a t) : string= 
    match env with 
      [] -> ""
    | fr::env -> 
      "["^(String.concat "," (List.map fst (S.bindings fr)))^"]"^
      (varsOf env) *)
(* 
  let pp_pair (pf : Format.formatter) ((x, v) : string * 'a) : unit =
    Format.fprintf pf "(%s:%a)" x V.pp_t v *)
    
  let pp_frame (pp_a :Format.formatter -> 'a -> unit) (pf : Format.formatter) (fr : 'a frame) : unit = 
    Format.fprintf pf "[%a]" (Format.pp_print_list (pp_print_pair Format.pp_print_string pp_a)) (S.bindings fr)

  let pp_t (pp_a :Format.formatter -> 'a -> unit) (pf : Format.formatter) (env : 'a t) : unit =
      Format.fprintf pf "%a" (Format.pp_print_list (pp_frame pp_a)) env 

  let top env = match env with [] -> None | h ::t -> Some (h,t)
  (* [record env (x,a)] : augment env with a mapping from a with x *)
  (* it is undefined if x is already defined in env or if env is empty *)
  let record (env : 'a t) ((x,a) : string * 'a)  : 'a t option =
  match env with
    | [] -> None
    | h :: t ->
        if S.exists (fun y _ -> x = y) h then None
        else Some (S.add x a h :: t)

  (** [fetchLoc env x] : returns the memory H.address associated with a variable *)
  (* it returns the value mapped by the first element of env defining x *)
  let getVariable (env : 'a t) (x : string) : 'a option =
    let rec aux (env : 'a t) =
      match env with
      | [] -> None
      | blockvar :: env -> (
          match S.find_opt x blockvar with None -> aux env | _ as x -> x)
    in aux env

  let allValues (e : 'a frame) : 'a list = 
      S.fold (fun _ x y -> x::y) e [] 

  let activate (e : 'a t) (fr : 'a frame) =
    fr :: e 

let merge (fr1 : 'a frame) (fr2 : 'a frame) : 'a frame = 
    S.union (fun _ _ y -> Some y) fr1 fr2

  let push (e : 'a t) (fr : 'a frame) :'a t option =
    match e with 
      | [] -> None 
      | fr'::e' -> Some (S.union (fun _ _ y -> Some y) fr fr' :: e')

  let deactivate (e :'t) : ('a list *  'a t) option = 
    match e with 
      [] -> None 
      | h::t -> Some (S.fold (fun _ x y -> x::y) h [], t)

  let concat l1 l2 = l1 @ l2
end
