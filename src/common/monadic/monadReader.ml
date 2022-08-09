open Monad


module type S = functor (M:Monad) (Env: Type)-> sig
  include MonadTransformer
  val read : Env.t t
end  with type 'a t = Env.t -> 'a M.t  and type 'a old_t := 'a M.t 


module T : S = functor (M:Monad) (Env: Type) -> struct
  open MonadSyntax(M)

  type env = Env.t

  type 'a t = env -> 'a M.t

  let pure (x:'a) : 'a t = fun _ -> M.pure x

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = 
    fun e -> let+ x = x e in f x

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    fun e -> let* f = f e in fmap f x e

  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    fun e -> let* x = x e in f x e

  let lift (x:'a M.t) : 'a t = fun _ -> let+ x in x

  let read = fun (e:env) -> M.pure e
end

module M = T(MonadIdentity)