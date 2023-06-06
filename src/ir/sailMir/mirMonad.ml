open AstMir
open Common 

module E = Error.Logger
module ES = MonadState.T(E)(VE)
module ESC = struct 
  include MonadState.CounterTransformer(ES)
  let error e = E.throw e |> ES.lift |> lift

  let log e = E.log e |> ES.lift |> lift
  let ok e = E.pure e |> ES.lift |> lift
  let get_env = ES.get |> lift    
  let update_env f = ES.update f |> lift
  let set_env e = ES.set e |> lift
  let update_var l f id = ES.update (fun e -> VE.update_var e l id f ) |> lift
  let declare_var l id v = ES.update (fun e -> VE.declare_var id (l,v) e) |> lift
  let find_var id = bind get_env (fun e -> VE.get_var id e |> pure) 

  let throw_if_none opt e = E.throw_if_none opt e |> ES.lift |> lift

end
