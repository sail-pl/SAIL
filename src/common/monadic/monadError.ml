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

module type ErrorMonad  = sig 
  include Monad 

  type error
  val throwError : error -> 'a t
  val catchError : 'a t -> (error -> 'a t) -> 'a t
end

module ErrorMonadOption : ErrorMonad with type 'a t = 'a option and type error = unit = struct 

  include MonadOption.M
  
  type error = unit 

  let throwError () = None 

  let catchError x f = match x with Some _ -> x | None -> f () 
  
end


module ErrorMonadEither = struct

  module Make (T : Type) : ErrorMonad with type 'a t = (T.t, 'a) Either.t and type error = T.t = struct 
    include MonadEither.Make(T)
    
    type error = T.t

    let throwError e = Either.Left e 

    let catchError x f = 
      match x with Either.Right _ -> x | Either.Left e -> f e 

  end 
end