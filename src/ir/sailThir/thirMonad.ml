open Common
open TypesCommon

module E = Error.Logger

module V = (
  struct 
    type t = bool * sailtype
    let string_of_var (_,t) = string_of_sailtype (Some t)
    let to_var _ (m:bool) (t:sailtype) = m,t
  end
)

module THIREnv = SailModule.SailEnv(V)

module ES = struct
  include MonadState.T(E)(THIREnv)

  let get_decl id ty = bind get (fun e -> THIREnv.get_decl e id ty |> pure) 

  let get_var id = bind get (fun e -> THIREnv.get_var e id |> pure) 


  let throw e = E.throw e |> lift
  let log e = E.log e |> lift
  let log_if b e = E.log_if b e |> lift
  let throw_if b e = E.throw_if b e |> lift

  let throw_if_none opt e = E.throw_if_none opt e |> lift


  let run e = E.bind e (fun e -> fst e |> E.pure)

  let recover (type a) (_default:a) (_e: a t) : a t =
     Logs.info (fun m -> m "todo recover ES");
     _e
end