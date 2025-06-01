open Common

module Make(MonoidSeq : Monad.Monoid) = struct
  module V : Env.Variable with type t = Env.TypeEnv.t -> (string * Env.TypeEnv.t)  = (
    struct 
      type t = Env.TypeEnv.t -> (string * Env.TypeEnv.t)
      let string_of_var _v : string = ""
      let param_to_var (p:TypesCommon.param) : t = fun te -> Env.TypeEnv.get_id p.ty te
    end
  )

  module THIREnv = SailModule.SailEnv(V)

  module M = struct
    module E = Logging.Logger
    module ES = struct
      include MonadState.T(E)(struct type t = THIREnv.t * Env.TypeEnv.t end)

      let get_decl id ty = bind get (fun (e,_) -> THIREnv.get_decl id ty e |> pure) 
      let get_var id = bind get (fun (e,_) -> THIREnv.get_var id e |> pure) 
      let throw e = E.throw e |> lift
      let log e = E.log e |> lift
      let log_if b e = E.log_if b e |> lift
      let throw_if e b = E.throw_if e b |> lift
      let throw_if_none e opt  = E.throw_if_none e opt  |> lift
      let run (f : 'a -> 'b t) env = fun x -> E.bind (f x env) (fun (e,(_,s)) -> E.pure (e,s))
      let recover (type a) (default:a) (x: a t) : a t = 
        fun e -> E.recover (default,e) (x e)
    
      let get_type_from_id id = bind get (fun (_,te) -> Env.TypeEnv.get_from_id id te |> lift)

      let get_type_id ty : string t = fun (e,te) -> let id,te = Env.TypeEnv.get_id ty te in E.pure (id,(e,te))
        
    end
    
  module ESC = struct 
    include MonadState.CounterTransformer(ES)(struct type t = int let succ = Int.succ let init = 0  end)

    let get_decl id ty = ES.get_decl id ty |> lift
    let get_var id = ES.get_var id |> lift
    let throw_if_none e opt = ES.throw_if_none e opt |> lift
    let throw_if e b = ES.throw_if e b |> lift
    let throw e  = ES.throw e |> lift
    let recover def x = ES.recover def x |> lift
    let log e = ES.log e |> lift 
    let update_env f = ES.update f |> lift

    let run (f : 'a -> 'b t) = fun x e -> E.bind (ES.run (f x) e 0) (fun ((res,_),e) -> E.pure (res,e)) 
  end

    include MonadWriter.MakeTransformer(ESC)(MonoidSeq)
    let get_decl id ty = ESC.get_decl id ty |> lift
    let get_var id = ESC.get_var id |> lift
    let throw_if_none e opt = ESC.throw_if_none e opt |> lift
    let throw_if e b = ESC.throw_if e b |> lift
    let throw e  = ESC.throw e |> lift
    let recover def x = ESC.recover def x |> lift
    let log e = ESC.log e |> lift 

    let get_env = ES.get |> ESC.lift |> lift

    let set_env e = ES.set e |> ESC.lift |> lift

    let get_type_from_id id = ES.get_type_from_id id |> ESC.lift |> lift
    let get_type_id ty : string t = ES.get_type_id ty|> ESC.lift |> lift
    let fresh_fvar = bind (ESC.fresh |> lift) (fun n -> pure @@ "__f" ^ string_of_int n)
  end
end