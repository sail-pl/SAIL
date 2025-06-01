open Monad
module MakeTransformer (M : Monad) (T : Type) : MonadTransformer 
  with  type 'a old_t = 'a M.t and   type 'a t = (T.t, 'a) Either.t M.t = struct

  open Either
  open MonadSyntax(M)

  type 'a old_t = 'a M.t

  type 'a t = (T.t, 'a) Either.t old_t

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t = 
    let+ x in match x with 
    | Right r -> Either.right (f r)
    | Left l -> Left l

  let pure (x: 'a) : 'a t = Right  x |> M.pure

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    let* f in match f,x with
    | Right f, x -> fmap f x
    | Left l, _ ->  Left l |> M.pure


  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    let* x in match x with
    | Right x -> f x
    | Left l ->  Left l |> M.pure

  let lift (x:'a M.t) : 'a t = let+ x in right x

end

module Make = MakeTransformer(MonadIdentity)






