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

module type Monoid = sig 
  type t 
  val mempty : t
  val mconcat : t -> t -> t
end

module MonoidList (T : Type) : Monoid with type t = T.t list = struct
  type t = T.t list
  let mempty = [] 
  let mconcat = (@)
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
  let (<$>) = M.fmap
  let (<&>) = fun x f -> M.fmap f x
  let (>>=) = M.bind
  let (>>|) x f = x >>= fun x -> f x |> M.pure
  (* let (>>) x (lazy y) = x >>= fun _ -> y *)
  (* 
  requires lazy, otherwise y is evaluated even if the behaviour of bind doesn't execute its right argument 
    however lazy values are not handled by coq_of_ocaml...
  *)
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

module type Sequencable = sig
  type t 
  type seq_ty 
  val to_seq :  t -> seq_ty Seq.t
  val of_seq :  seq_ty Seq.t -> t 
end

module MonadFunctions (M : Monad) = struct 
  open MonadSyntax (M)
  open MonadOperator (M)

  module SeqM = struct 
    let rec map (f : 'a -> 'b M.t) (s : 'a Seq.t) : 'b Seq.t M.t =
      match s () with
      | Nil -> return Seq.empty
      | Cons (x, next) ->
          let* u = f x in 
          let+ l' = map f next in
          Seq.cons u l'

    let rec iter (f : 'a -> unit M.t) (s : 'a Seq.t) : unit M.t =
      match s () with
      | Nil -> return ()
      | Cons (x, next) ->
          let* () = f x in 
          iter f next 

      let rec iter2 (f : 'a -> 'b -> unit M.t ) (s1 : 'a Seq.t) (s2 : 'b Seq.t) : unit M.t =
        match s1 () with
        | Nil -> return ()
        | Cons (x, xs) ->
            match s2 () with
            | Nil -> return ()
            | Cons (y, ys) ->
                f x y >>= (fun () -> iter2 f xs ys)

    let rec fold_left (f : 'a -> 'b -> 'a M.t) (acc : 'a) (s : 'b Seq.t) : 'a M.t =
      match s () with
      | Nil -> return acc
      | Cons (x, next) ->
          let* acc = f acc x in 
          fold_left f acc next 

    let rec fold_left_map (f : 'a -> 'b -> ('a * 'c) M.t) (accu : 'a) (s : 'b Seq.t) : ('a * 'c Seq.t) M.t = 
    match s () with
    | Seq.Nil -> return (accu, Seq.empty)
    | Cons (x,l) ->
        let* accu,u = f accu x in
        let+ accu,l' = fold_left_map f accu l in
        accu,Seq.cons u l'

    let sequence (s : 'a M.t Seq.t) : 'a Seq.t M.t  = map Fun.id s
  end

  module MakeFromSequencable(S : Sequencable) = struct
    let map (f : 'a -> 'b M.t) (s : S.t) = let+ s = SeqM.map f (S.to_seq s) in S.of_seq s
    let fold (f : 'a -> 'b -> 'a M.t) (acc : 'a) (s : S.t) = SeqM.fold_left f acc (S.to_seq s)
    let iter (f : 'a -> unit M.t) (s : S.t) = SeqM.iter f (S.to_seq s)
  
  end

  module MakeOrderedFunctions(Order : sig type t val compare : t -> t -> int end ) = struct
    module MapM = struct
      module MMap = Map.Make(Order)
      let map (f : MMap.key -> 'a -> 'b M.t) (m : 'a MMap.t) : ('b MMap.t) M.t = 
      let* l' = SeqM.map (fun (id,x) -> let+ res = f id x in id,res) (MMap.to_seq m) in 
      return (MMap.of_seq l')


      let iter(f : MMap.key -> 'a -> unit M.t) (m : 'a MMap.t) : unit M.t = 
        let rec aux (l : (MMap.key * 'a) Seq.t) : unit M.t =
          match l () with
          | Seq.Nil -> return ()
          | Seq.Cons ((k, a), v) -> f k a >>= (fun () ->aux v)
        in  
        aux (MMap.to_seq m) 
    end

    module SetM = struct
      module MSet = Set.Make(Order)
      (* limitation : output Set must be of the same as the input one *)
      let map (f : Order.t -> Order.t M.t) (m : MSet.t) : MSet.t M.t = 
        let+ l' = SeqM.map f (MSet.to_seq m) in MSet.of_seq l'

      let fold ?(rev=false) (f : 'a -> Order.t -> 'a M.t) (acc : 'a) (m : MSet.t) : 'a M.t = 
        let to_seq = if rev then MSet.to_rev_seq else MSet.to_seq in
        SeqM.fold_left f acc (to_seq m) 

      let fold_left_map ?(rev=false) (f : 'a -> Order.t -> ('a  * 'b) M.t) (acc : 'a) (m : MSet.t) : ('a * MSet.t )M.t = 
        let to_seq = if rev then MSet.to_rev_seq else MSet.to_seq in
        let+ acc,l' = SeqM.fold_left_map f acc (to_seq m) in acc,MSet.of_seq l'
    end
  end

  module ListM = struct
    let rec map (f : 'a -> 'b M.t) (l : 'a list) : ('b list) M.t =
      match l with 
      | [] -> return []
      | h::t -> let+ u = (f h) and* t = map f t in u::t
          
          
    let rec iter (f : 'a -> unit M.t)  (l : 'a list) : unit M.t = 
        match l with 
        | [] -> return ()
        | h::t -> f h >>= (fun () -> iter f t)

    let rec iter2 f l1 l2 =
      match (l1, l2) with
        ([], []) -> return ()
      | (a1::l1, a2::l2) -> let* () = f a1 a2 in iter2 f l1 l2
      | (_, _) -> invalid_arg "ListM.iter2"

    let rec fold_left (f : 'a -> 'b -> 'a M.t) (x : 'a) (l : 'b list) : 'a M.t = 
      match l with 
        | [] -> return x 
        | h :: t -> fold_left f x t >>=  (Fun.flip f) h      
        
    let fold_left_map (f : 'a -> 'b -> ('a * 'c) M.t) (accu : 'a) (l : 'b list) : ('a * 'c list) M.t = 
      let rec aux accu l_accu = function
      | [] -> return (accu, List.rev l_accu)
      | x :: l ->
          let* accu, x = f accu x in
          aux accu (x :: l_accu) l in
      aux accu [] l

    
    let rec fold_right (f : 'a -> 'b -> 'b M.t) (l : 'a list) (x : 'b) : 'b M.t = 
      match l with 
        | [] -> return x
        | h :: t -> f h x >>= fold_right f t

    let sequence (l : 'a M.t list) : 'a list M.t = map Fun.id l
  end

  let pairMap1 (f : 'a -> 'b M.t) ((x,y) : 'a * 'c) :('b * 'c) M.t =
      let+ x = f x in (x, y)


  let pairMap2 (f : 'c -> 'b M.t) ((x,y) : 'a * 'c) :('a * 'b) M.t =
      let+ y = f y in x, y
end