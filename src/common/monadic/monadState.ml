open Monad



module type S = functor (M:Monad) (State: Type) -> sig
  include MonadTransformer

  val get : State.t t
  val set : State.t -> unit t
  val update : (State.t -> State.t M.t) -> unit t


end  with type 'a t = State.t -> ('a  * State.t) M.t  and  type 'a old_t  := 'a M.t 

module T : S  = functor (M:Monad) (State: Type) -> struct
  open MonadSyntax(M)

  type 'a t = State.t -> ('a * State.t) M.t

  let pure (x:'a) : 'a t = fun s -> M.pure (x,s)

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = 
    fun s -> let+ x,xs = x s in f x,xs

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    fun s -> let* f,fs = f s in fmap f x fs

  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    fun s -> let* x,xs = x s in f x xs

  let lift (x:'a M.t) : 'a t = fun s -> let+ x in x,s

  let get = fun s -> M.pure (s,s)
  let set new_st : unit t =  fun _ -> M.pure ((),new_st)

  let update (f : (State.t -> State.t M.t)) : unit t = fun s -> M.bind (f s) (fun x -> M.pure ((),x))
end

module M = T(MonadIdentity)



module CounterTransformer  = functor (M:Monad) -> struct
  include T(M)(struct type t = int end)

  let tick : unit t = fun n -> set (succ n) n
  let get : int t = get
  let fresh : int t = bind get (fun n -> bind tick (fun () ->  pure n))

  
  let run (f : 'a t) = M.bind (f 0) (fun (r,_) -> M.pure r) (* generalize to all monads ?  *)
end

module Counter = CounterTransformer(MonadIdentity)