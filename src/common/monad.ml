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

open Type

module type Functor = sig 
  type 'a t 
  val fmap : ('a -> 'b) -> 'a t  -> 'b t
end

module type Applicative = sig
include Functor
  val pure : 'a -> 'a t  
  val (<*>) : ('a -> 'b ) t -> 'a t -> 'b t
end 

module type Monad = sig
  include Applicative
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (>>|) : 'a t -> ('a -> 'b) -> 'b t
end

module MonadSyntax (M : Monad )= struct 
  let return = M.pure

  let (let*) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t = M.(>>=)

  let (and*) x y = 
    let* x = x in let* y = y in return (x,y)

  let (let+) : 'a M.t -> ('a -> 'b) -> 'b M.t = M.(>>|)
  let (and+) x y =
    let+ x = x in let+ y = y in return (x,y)

end





module MonadFunctions (M : Monad) = struct 
  open TypesCommon 

  let mapMapM (f : 'a -> 'b M.t) (m : 'a FieldMap.t) : ('b FieldMap.t) M.t = 
  let open MonadSyntax (M) in
  let rec aux (l : (string * 'a) Seq.t) : (string * 'b) Seq.t M.t =
    match l () with
    | Seq.Nil -> return (fun () -> Seq.Nil)
    | Seq.Cons ((x, a), v) ->
        let* u = f a in 
        let* l' = aux v in
        return (fun () -> Seq.Cons ((x,u),l' ))
  in  
  let* l' = aux (FieldMap.to_seq m) in 
  return (FieldMap.of_seq l')
  
  let rec listMapM (f : 'a -> 'b M.t) (l : 'a list) : ('b list) M.t = 
    let open M in
    let open MonadSyntax(M) in
    match l with 
      | [] -> return []
      | h::t -> (f h) >>= (fun h -> listMapM f t >>= fun t -> return (h::t))  

  let rec foldLeftM (f : 'a -> 'b -> 'a M.t) (x : 'a) (l : 'b list) : 'a M.t = 
    let open M in
    let open MonadSyntax(M) in
    match l with 
      | [] -> M.pure x 
      | h :: t -> foldLeftM f x t >>=  (Fun.flip f) h      

  let rec sequence (l : 'a M.t list) : 'a list M.t =
    let open MonadSyntax(M) in
    match l with
    | [] -> M.pure []
    | h :: t -> 
      let* h = h and* t = sequence t in M.pure (h::t)

  let pairMap1 (f : 'a -> 'b M.t) ((x,y) : 'a * 'c) :('b * 'c) M.t =
    let open M in
    let open MonadSyntax(M) in
      f x >>= (fun x -> return (x, y))


  let pairMap2 (f : 'c -> 'b M.t) ((x,y) : 'a * 'c) :('a * 'b) M.t =
    let open M in
    let open MonadSyntax(M) in
      f y >>= (fun y -> return (x, y))
end

module MonadEither = struct 
  
  module  Make (T : Type) : Monad with type 'a t = (T.t, 'a) Either.t = struct

    type 'a t = (T.t, 'a) Either.t
    let fmap f x = 
      match x with 
        | Either.Left e -> Either.Left e
        | Either.Right x -> Either.Right (f x)

    let pure x = Either.Right x 

    let (<*>) f x = 
      match (f, x) with 
        | Either.Right f, x -> fmap f x
        | Either.Left e, _ -> Either.Left e
    
  let (>>=)  x f = 
    match x with 
      | Either.Right x -> f x 
      | Either.Left e -> Either.Left e


  let (>>|)  x f = 
  match x with 
    | Either.Right x -> f x |> pure
    | Either.Left e -> Either.Left e
end

  
end