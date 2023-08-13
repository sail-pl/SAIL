open AstMir
open Common 

module M = struct 
  module E = Error.Logger
  module ES = MonadState.T(E)(VE)
  module C = struct type t = {scoped_vars : int; bblocks: int; vars : int} end
  module ESC = MonadState.T(ES)(C)

  
  include (ESC : Monad.Monad with type 'a t = 'a ESC.t)

  let error e = E.throw e |> ES.lift |> ESC.lift 
  let log e = E.log e |> ES.lift |> ESC.lift 
  let ok e = E.pure e |> ES.lift |> ESC.lift
  let get_env = ES.get |> ESC.lift 
  let update_env f = ES.update f |> ESC.lift
  let set_env e = ES.set e |> ESC.lift
  let update_var l f id = ES.update (VE.update_var l id f) |> ESC.lift
  let declare_var l id v = ES.update (VE.declare_var id (l,v)) |> ESC.lift
  let find_var id = bind get_env (fun e -> VE.get_var id e |> pure) 
  let throw_if_none opt e = E.throw_if_none opt e |> ES.lift |> ESC.lift
  let run (f:'a -> 'b t) x env = E.bind (f x {scoped_vars=0; bblocks=0;vars=0} env) (fun ((res,_),_) -> E.pure res)

  let fresh_block =  bind ESC.get (fun n -> bind (fun n -> ESC.set {n with bblocks=n.bblocks + 1} n) (fun () ->  pure n.bblocks))
  let current_block = bind ESC.get (fun n -> pure n.bblocks)

  let fresh_scoped_var = bind ESC.get (fun n -> bind (fun n -> ESC.set {n with scoped_vars=n.scoped_vars + 1} n) (fun () ->  pure n.scoped_vars))
  let current_scoped_var = bind ESC.get (fun n -> pure n.scoped_vars)

  let fresh_var = bind ESC.get (fun n -> bind (fun n -> ESC.set {n with vars=n.vars + 1} n) (fun () ->  pure n.vars))
  let current_var = bind ESC.get (fun n -> pure n.vars)


end
