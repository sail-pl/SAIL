open Error
open Monad
open TypesCommon

open MonadFunctions(Logger)
open MonadSyntax(Logger)
open MonadOperator(Logger)


module type Pass = sig
  val name : string
  type input
  type output

  val transform : input -> output
end


module type ModulePass = sig
  type in_body
  type out_body  

  include Pass with type input := in_body SailModule.t and type output := out_body SailModule.t Logger.t
end



module type S = sig
  type in_body
  type out_body
  include Pass with type input := in_body SailModule.t Logger.t and type output := out_body SailModule.t Logger.t
end



module Progression = struct 
  type (_,_) t = 
  | Transform : ('a -> 'b) * ('b,'c) t -> ('a, 'c) t
  | Done : ('a,'a) t

  let run p i =
    let rec aux : type a b. (a,b) t -> a -> b = fun pipeline input ->
    match pipeline with
    | Done -> input
    | Transform (f,tail) -> aux tail (f input)
    in aux p i

  let finish = Done
  
  let (@>) f pipeline = Transform (f,pipeline) 
end




module Make (T: ModulePass) : S with type in_body = T.in_body and type out_body = T.out_body  = 
struct
  let name = T.name
  type in_body = T.in_body
  type out_body = T.out_body
  let transform (sm: T.in_body SailModule.t Logger.t) : T.out_body SailModule.t Logger.t = 
    let* sm = sm |> Logger.fail in 
    Logs.info (fun m -> m "Lowering module '%s' to '%s'" sm.md.name name);
    T.transform sm
end



module MakeFunctionPass 
  (V : Env.Variable) 
  (T: 
    sig 
    val name : string 

    type m_in
    type m_out

    type p_in
    type p_out
    
    
    val lower_method : m_in * method_sig -> SailModule.SailEnv(V).t -> (m_in,p_in) SailModule.methods_processes SailModule.t -> (m_out * SailModule.SailEnv(V).D.t) Logger.t 


    val lower_process : p_in process_defn -> SailModule.SailEnv(V).t -> (m_in,p_in) SailModule.methods_processes SailModule.t -> (p_out * SailModule.SailEnv(V).D.t) Logger.t 

    val preprocess : (m_in,p_in) SailModule.methods_processes SailModule.t -> (m_in,p_in) SailModule.methods_processes SailModule.t Logger.t
    end)  
  : S with type in_body = (T.m_in, T.p_in) SailModule.methods_processes and type out_body = (T.m_out,T.p_out) SailModule.methods_processes = 
struct
  let name = T.name

  type in_body = (T.m_in,T.p_in) SailModule.methods_processes
  type out_body = (T.m_out,T.p_out) SailModule.methods_processes

  module VEnv = SailModule.SailEnv(V)

  let lower_method (m:T.m_in method_defn) (sm : (T.m_in,T.p_in) SailModule.methods_processes SailModule.t) : (VEnv.D.t  * T.m_out method_defn) Logger.t = 
    match m.m_body with
    | Right f -> 
      let* ve = VEnv.get_start_env sm.declEnv m.m_proto.params in
      let+ b,d = T.lower_method (f,m.m_proto) ve sm in 
      d,{ m with m_body=Either.right b }
    | Left x ->  Logger.pure (sm.declEnv,{ m with m_body = Left x}) (* nothing to do for externals *)


  let lower_process (p: T.p_in process_defn) (sm : (T.m_in,T.p_in) SailModule.methods_processes SailModule.t) : (VEnv.D.t * T.p_out process_defn ) Logger.t  = 
    let start_env = VEnv.get_start_env sm.declEnv (fst p.p_interface) in
    let* ve = start_env in
    let+ p_body,d = T.lower_process p ve sm in
    d,{ p with p_body}



  let transform (sm : (T.m_in, T.p_in) SailModule.methods_processes SailModule.t Logger.t)  : (T.m_out, T.p_out) SailModule.methods_processes SailModule.t Logger.t =
    let* sm = sm >>= T.preprocess in
    Logs.info (fun m -> m "Lowering module '%s' to '%s'" sm.md.name name);
    (
    let* declEnv,methods = ListM.fold_left_map 
                          (fun declEnv methd -> lower_method methd {sm with declEnv}) 
                          sm.declEnv sm.body.methods |> Logger.recover (sm.declEnv,[]) 
    in
    let+ declEnv,processes = ListM.fold_left_map 
                              (fun declEnv proccess -> lower_process proccess {sm with declEnv}) 
                              declEnv sm.body.processes |> Logger.recover (sm.declEnv,[]) in

    { sm with body=SailModule.{processes; methods} ; declEnv }

    ) |> Logger.fail
end