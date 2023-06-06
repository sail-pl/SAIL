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

module type Writer = sig 
  include MonadTransformer
  type elt 
  val write : elt -> unit t
end


module MakeTransformer (M : Monad) (T : Monoid)  : Writer with type 'a t = ('a * T.t) M.t and type elt = T.t  and type 'a old_t = 'a M.t = struct 
  open MonadSyntax(M)

  type elt = T.t

  type 'a old_t = 'a M.t

  type 'a t = ('a * T.t) old_t


  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = let+ x,l = x in (f x, l)
  let pure (x: 'a) : 'a t = M.pure (x,T.mempty)

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    let+ f,l1 = f and* v,l2 = x in f v,T.mconcat l1 l2


  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    let* v,l1 = x in 
    let+ v,l2 = f v in v, T.mconcat l1 l2

  let lift (x:'a M.t) : 'a t = let+ x in x,T.mempty

  let write (x:elt) : 'a t = M.pure ((),x)
end

module Make = MakeTransformer(MonadIdentity)
