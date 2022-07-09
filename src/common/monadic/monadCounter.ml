open Monad


module type Counter = functor (M:Monad) -> sig
  include MonadTransformer
  val tick :  unit t
  val get : int t
  val fresh : int t
end  with type 'a t = int -> ('a  * int) M.t  and  type 'a old_t  := 'a M.t

module T : Counter = functor (M:Monad) -> struct

  open MonadSyntax(M)

  type 'a t = int -> ('a  * int) M.t

  let pure (x:'a) : 'a t = fun n -> M.pure (x,n)

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = 
    fun n ->  let+ v,c = x n in  f v,c

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    fun n -> 
      let* f,c = f n in fmap f x c


  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t =
    fun n -> 
      let* v,c = x n in f v c
        

  let lift (x:'a M.t) : 'a t = fun n -> let+ x in x,n

  let tick  : unit t = fun n -> M.pure ((), n+1)

  let get : int t = fun n -> M.pure (n,n)

  let fresh : int t = bind get (fun n -> bind tick (fun () ->  pure n))

end

module M = T(MonadIdentity)