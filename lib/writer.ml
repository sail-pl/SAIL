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
open Monoid

module Writer = struct

  module type Writer = sig 
    include Monad
    type elt 
    val write : elt -> unit t
  end

  module Make (T : Monoid) : Writer with type 'a t = 'a * T.t and type elt = T.t = struct 
    type 'a t = 'a * T.t

    type elt = T.t

    let fmap f (x, l) = (f x, l)
    let pure x = (x,T.mempty)

    let (<*>) (f, l1) (x, l2) = (f x, T.mconcat l1 l2)

    let (>>=) (x, l) f = let (y,l') = f x in (y, T.mconcat l l')

    let write : T.t -> 'a t = fun a  -> ((), a) 
  end
end