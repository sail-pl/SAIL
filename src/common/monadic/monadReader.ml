open Monad

module type Read = sig
  type env
  type id
  type elt
  val read : id -> env -> elt
end



module type S = functor (M:Monad) (R: Read)-> sig
  include MonadTransformer

  val read : R.id -> R.elt t

end  with type 'a t = R.env -> 'a M.t  and  type 'a old_t  := 'a M.t 


module T : S = functor (M:Monad) (R:Read) -> struct
  open MonadSyntax(M)

  type 'a t = R.env -> 'a M.t

  let pure (x:'a) : 'a t = fun _ -> M.pure x

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = 
    fun e -> let+ x = x e in f x

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    fun e -> let* f = f e in fmap f x e

  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    fun e -> let* x = x e in f x e

  let lift (x:'a M.t) : 'a t = fun _ -> let+ x in x

  let read (id:R.id) = fun e -> M.pure (R.read id e)
end

module M = T(MonadIdentity)