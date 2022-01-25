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
  val (<*>) : ('a -> 'b ) t -> 'a t -> 'b t
end 

module type Monad = sig
  include Applicative
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module MonadSyntax (M : Monad )= struct 
  let (let*) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t = M.(>>=)
  let return = M.pure
  let (and*) x y = 
    let* x = x in let* y = y in M.pure (x,y)
end

module FunctorOption : Functor with type 'a t = 'a option = struct 
  type 'a t = 'a option
  let fmap f x = match x with Some x -> Some (f x) | None -> None 
end 

module ApplicativeOption : Applicative with type 'a t = 'a option = struct 
  
  include FunctorOption
  let pure x = Some x
  let (<*>) f x = match (f,x) with (Some f, Some x) -> Some (f x) | _ -> None 
end 

module MonadOption : Monad with type 'a t = 'a option = struct 
  include ApplicativeOption
  let (>>=) x f = match x with Some x -> f x | None -> None 
end

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

module MonadFunctions (M : Monad) = struct 
  
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


