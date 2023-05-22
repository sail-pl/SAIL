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

module type Type = sig 
  type t
end

module type Functor = sig 
  type 'a t 
  val fmap : ('a -> 'b) -> 'a t  -> 'b t
end

module type Applicative = sig
include Functor
  val pure : 'a -> 'a t  
  val apply : ('a -> 'b ) t -> 'a t -> 'b t
end 

module type Monad = sig
  include Applicative
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module type MonadTransformer = sig
  include Monad
  type 'a old_t
  val lift : 'a old_t -> 'a t
end

module MonadIdentity : Monad with type 'a t = 'a = struct
  type 'a t = 'a
  let pure x = x

  let fmap f x = f x

  let apply = fmap

  let bind x f = f x
end

module MonadOperator (M : Monad) = struct
  let (<*>) = M.apply
  let (>>=) = M.bind
  let (>>|) x f = x >>= fun x -> f x |> M.pure
  let (>>) x y = x >>= fun _ -> y
end

module MonadSyntax (M : Monad ) = struct 
  open M
  open MonadOperator(M)
  let return = pure

  let (let*) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t = M.bind

  let (and*) x y = 
    let* x = x in let* y = y in return (x,y)

  let (let+) : 'a M.t -> ('a -> 'b) -> 'b M.t = (>>|)
  let (and+) x y =
    let+ x = x in let+ y = y in return (x,y)

end


module MonadFunctions (M : Monad) = struct 


  module MakeOrderedFunctions(Order : sig type t val compare : t -> t -> int end ) = struct
    module MMap = Map.Make(Order)
    module MSet = Set.Make(Order)

    let mapMapM (f : 'a -> 'b M.t) (m : 'a MMap.t) : ('b MMap.t) M.t = 
    let open MonadSyntax (M) in
    let rec aux (l : (MMap.key * 'a) Seq.t) : (MMap.key * 'b) Seq.t M.t =
      match l () with
      | Seq.Nil -> return (fun () -> Seq.Nil)
      | Seq.Cons ((x, a), v) ->
          let* u = f a in 
          let+ l' = aux v in
          fun () -> Seq.Cons ((x,u),l' )
    in  
    let* l' = aux (MMap.to_seq m) in 
    return (MMap.of_seq l')


    let mapIterM (f : MMap.key -> 'a -> unit M.t) (m : 'a MMap.t) : unit M.t = 
      let open MonadSyntax (M) in
      let rec aux (l : (MMap.key * 'a) Seq.t) : unit M.t =
        match l () with
        | Seq.Nil -> return ()
        | Seq.Cons ((k, a), v) ->
            let* () = f k a in 
            aux v
      in  
      aux (MMap.to_seq m) 


      (* limitation : output Set must be of the same as the input one *)
      let setMapM (f : Order.t -> Order.t M.t) (m : MSet.t) : MSet.t M.t = 
        let open MonadSyntax (M) in
        let rec aux (l : MSet.elt Seq.t) : MSet.elt Seq.t M.t =
          match l () with
          | Seq.Nil -> return (fun () -> Seq.Nil)
          | Seq.Cons (a, v) ->
              let* u = f a in 
              let+ l' = aux v in
              fun () -> Seq.Cons (u,l' )
        in  
        let* l' = aux (MSet.to_seq m) in 
        return (MSet.of_seq l')
  end

  let rec listMapM (f : 'a -> 'b M.t) (l : 'a list) : ('b list) M.t = 
    let open MonadSyntax (M) in
    match l with 
      | [] -> return []
      | h::t -> let+ u = (f h) and* t = listMapM f t in u::t
      
      
  let rec listIterM (f : 'a -> unit M.t)  (l : 'a list) : unit M.t = 
      let open MonadSyntax (M) in
      match l with 
      | [] -> return ()
      | h::t -> let* () = (f h) in listIterM f t

  let rec foldLeftM (f : 'a -> 'b -> 'a M.t) (x : 'a) (l : 'b list) : 'a M.t = 
    let open M in
    let open MonadOperator(M) in
    match l with 
      | [] -> pure x 
      | h :: t -> foldLeftM f x t >>=  (Fun.flip f) h      

      
  let foldLeftMapM (f : 'a -> 'b -> ('a * 'c) M.t) (accu : 'a) (l : 'b list) : ('a * 'c list) M.t = 
    let open MonadSyntax (M) in
    let rec aux accu l_accu = function
    | [] -> return (accu, List.rev l_accu)
    | x :: l ->
        let* accu, x = f accu x in
        aux accu (x :: l_accu) l in
    aux accu [] l

  
  let rec foldRightM (f : 'a -> 'b -> 'b M.t) (l : 'a list) (x : 'b) : 'b M.t = 
    let open M in
    let open MonadOperator(M) in
    match l with 
      | [] -> pure x
      | h :: t -> f h x >>= foldRightM f t

  let rec sequence (l : 'a M.t list) : 'a list M.t =
    let open MonadSyntax(M) in
    match l with
    | [] -> return []
    | h :: t -> 
      let* h = h and* t = sequence t in return (h::t)

  let pairMap1 (f : 'a -> 'b M.t) ((x,y) : 'a * 'c) :('b * 'c) M.t =
    let open MonadSyntax (M) in
      let+ x = f x in (x, y)


  let pairMap2 (f : 'c -> 'b M.t) ((x,y) : 'a * 'c) :('a * 'b) M.t =
    let open MonadSyntax (M) in
      let+ y = f y in x, y
end
  