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

module FunctorOption : Functor with type 'a t = 'a option = struct 
  type 'a t = 'a option
  let fmap f x = match x with Some x -> Some (f x) | None -> None 
end 

module ApplicativeOption : Applicative with type 'a t = 'a option = struct 
  
  include FunctorOption
  let pure x = Some x
  let (<*>) f x = match f with Some f -> fmap f x | _ -> None 
end 

module MonadOption : Monad with type 'a t = 'a option = struct 
  include ApplicativeOption
  let (>>=) x f = match x with Some x -> f x | None -> None 
end