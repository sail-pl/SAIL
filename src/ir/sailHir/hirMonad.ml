open Common

module Make(MonoidSeq : Monad.Monoid) = struct
  module V = struct 
    type t = unit
    let string_of_var _ = ""
    let to_var _ _ _ = ()
    end
  module HIREnv = SailModule.SailEnv(V)

  module E = Error.Logger
  module EC = MonadState.CounterTransformer(E)
  module ECS =  struct 
    include MonadState.T(EC)(HIREnv)
    let fresh = EC.fresh |> lift
    let run e = let e = EC.run e in E.bind e (fun (e,(_,s)) -> E.pure (e,s) )
    let find_var id = bind get (fun e -> HIREnv.get_var id e |> pure)
    let throw e = E.throw e |> EC.lift |> lift 
    let throw_if_none b e = E.throw_if_none b e |> EC.lift |> lift
    let log e = E.log e |> EC.lift |> lift 
    let log_if b e = E.log_if b e |> EC.lift |> lift 
    let throw_if b e = E.throw_if b e |> EC.lift |> lift 

    let get_decl id ty = bind get (fun e -> HIREnv.get_decl id ty e |> pure) 
  end

  module ECSW = struct
    include MonadWriter.MakeTransformer(ECS)(MonoidSeq)
    let get_decl id ty = ECS.bind ECS.get (fun e -> HIREnv.get_decl id ty e |> ECS.pure) |> lift
    let fresh = ECS.fresh |> lift
    let throw e = ECS.throw e |> lift 
    let log e = ECS.log e |> lift 
    let get_env = ECS.get |> lift
  end
end