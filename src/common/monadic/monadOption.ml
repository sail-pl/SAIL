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

open Monad 

module T (M: Monad )   : MonadTransformer 
  with type 'a t = 'a option M.t  and  type 'a old_t  := 'a M.t  = struct

  open MonadSyntax(M)

  type 'a t = 'a option M.t

  let pure x : 'a t = M.pure (Some x)

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t =
    let+ x in match x with 
    | Some v -> Some (f v) 
    | _ -> None

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    let* f in match f with 
    | Some f -> fmap f x
    | None -> M.pure None

  
  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    let* x in match x with 
    | Some x -> f x 
    | _ -> M.pure None

  let lift (x:'a M.t) : 'a t = let+ x in Some x
end


let list_of_option = function Some x -> [x] | None -> []

module M = T(MonadIdentity)