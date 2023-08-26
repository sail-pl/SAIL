open Logging
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
    
    
    val lower_method : m_in * method_sig -> (SailModule.SailEnv(V).t * Env.TypeEnv.t) -> (m_in,p_in) SailModule.methods_processes SailModule.t -> (m_out * SailModule.SailEnv(V).D.t * Env.TypeEnv.t) Logger.t 


    val lower_process : p_in process_defn -> (SailModule.SailEnv(V).t  * Env.TypeEnv.t)-> (m_in,p_in) SailModule.methods_processes SailModule.t -> (p_out * SailModule.SailEnv(V).D.t * Env.TypeEnv.t) Logger.t 

    val preprocess : (m_in,p_in) SailModule.methods_processes SailModule.t -> (m_in,p_in) SailModule.methods_processes SailModule.t Logger.t
    end)  
  : S with type in_body = (T.m_in, T.p_in) SailModule.methods_processes and type out_body = (T.m_out,T.p_out) SailModule.methods_processes = 
struct
  let name = T.name

  type in_body = (T.m_in,T.p_in) SailModule.methods_processes
  type out_body = (T.m_out,T.p_out) SailModule.methods_processes

  module VEnv = SailModule.SailEnv(V)

  let lower_method (m:T.m_in method_defn) (sm : (T.m_in,T.p_in) SailModule.methods_processes SailModule.t) : ((VEnv.D.t * Env.TypeEnv.t) * T.m_out method_defn) Logger.t = 
    match m.m_body with
    | Right f -> 
      let* ve = VEnv.get_start_env sm.declEnv m.m_proto.params in
      let+ b,d,t = T.lower_method (f,m.m_proto) (ve,sm.typeEnv) sm in 
      (d,t),{ m with m_body=Either.right b }
    | Left x ->  Logger.pure ((sm.declEnv,sm.typeEnv),{ m with m_body = Left x}) (* nothing to do for externals *)


  let lower_process (p: T.p_in process_defn) (sm : (T.m_in,T.p_in) SailModule.methods_processes SailModule.t) : ((VEnv.D.t * Env.TypeEnv.t) * T.p_out process_defn ) Logger.t  = 
    let* ve = VEnv.get_start_env sm.declEnv p.p_interface.p_params in
    let+ p_body,d,t = T.lower_process p (ve,sm.typeEnv) sm in
    (d,t),{ p with p_body}



  let transform (sm : (T.m_in, T.p_in) SailModule.methods_processes SailModule.t Logger.t)  : (T.m_out, T.p_out) SailModule.methods_processes SailModule.t Logger.t =
    let* sm = sm >>= T.preprocess in
    Logs.info (fun m -> m "Lowering module '%s' to '%s'" sm.md.name name);
    (
    let* (declEnv,typeEnv),methods = ListM.fold_left_map 
                          (fun (declEnv,typeEnv) methd -> lower_method methd {sm with declEnv ; typeEnv}) 
                          (sm.declEnv,sm.typeEnv) sm.body.methods |> Logger.recover ((sm.declEnv,sm.typeEnv),[]) 
    in
    let+ (declEnv,typeEnv),processes = ListM.fold_left_map 
                              (fun (declEnv,typeEnv) proccess -> lower_process proccess {sm with declEnv ; typeEnv}) 
                              (declEnv,typeEnv) sm.body.processes |> Logger.recover ((declEnv,typeEnv),[]) in

    { sm with body=SailModule.{processes; methods} ; declEnv; typeEnv }

    ) |> Logger.fail
end