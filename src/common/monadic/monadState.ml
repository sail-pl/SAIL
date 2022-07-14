open Monad


module type StateEnv = sig
  type state
  type id
  type elt

  val get : id -> state -> elt
  val set : id -> elt -> state -> state
end

module type S = functor (M:Monad) (S: StateEnv)-> sig
  include MonadTransformer

  val get : S.id -> S.elt t
  val set : S.id -> S.elt -> unit t


end  with type 'a t = S.state -> ('a  * S.state) M.t  and  type 'a old_t  := 'a M.t 

module T : S  = functor (M:Monad) (S:StateEnv) -> struct
  open MonadSyntax(M)

  type 'a t = S.state -> ('a * S.state) M.t

  let pure (x:'a) : 'a t = fun s -> M.pure (x,s)

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = 
    fun s -> let+ x,xs = x s in f x,xs

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    fun s -> let* f,fs = f s in fmap f x fs

  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    fun s -> let* x,xs = x s in f x xs

  let lift (x:'a M.t) : 'a t = fun s -> let+ x in x,s

  let get id = fun s -> M.pure (S.get id s,s)
  let set r x : unit t =  fun s -> M.pure ((),S.set r x s)

end

module M = T(MonadIdentity)



module CounterTransformer  = functor (M:Monad) -> struct
  module C = T(M)(
    struct 
      type state = int 
      type id = unit
      type elt = int 

      let set () _ n = succ n
      let get () = fun n -> n
    end
  )
  include C

  let tick : unit t = fun n -> set () n n
  let get : int C.t = get ()
  let fresh : int C.t = bind get (fun n -> bind tick (fun () ->  pure n))
end

module Counter = CounterTransformer(MonadIdentity)