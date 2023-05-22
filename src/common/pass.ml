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



(* module type AnalysisOutPass = sig
  type body
  type out_anl

  include Pass with type input := body SailModule.t and type output := out_anl Logger.t
end

module type SOut = sig
  type body
  type out_anl
  include Pass with type input := body SailModule.t Logger.t and type output := (out_anl * body SailModule.t) Logger.t
end



module type AnalysisInPass = sig
  type body
  type in_anl

  include Pass with type input = in_anl * body SailModule.t and type output := body SailModule.t Logger.t
end

module type SIn = sig
  type body
  type in_anl

  include Pass with type input := (in_anl * body SailModule.t) Logger.t and type output := body SailModule.t Logger.t
end

module MakeAnlIn (T: AnalysisInPass) : SIn with type body := T.body and type in_anl := T.in_anl = 
struct
  let name = T.name
  let transform (m: (T.in_anl * T.body SailModule.t) Logger.t) : T.body SailModule.t Logger.t = 
    let* m = m |> Logger.fail in 
    Logs.info (fun m -> m "Lowering using analysis to '%s'" name);
    T.transform m
end

module MakeAnlOut (T: AnalysisOutPass) : SOut with type body := T.body and type out_anl := T.out_anl = 
struct
  let name = T.name

  let transform (m: T.body SailModule.t Logger.t) : (T.out_anl * T.body SailModule.t) Logger.t = 
    let* m = m |> Logger.fail in 
    Logs.info (fun m -> m "Analysis : '%s'" name);
    let+ out = T.transform m in
    out,m
end *)


module Make (T: ModulePass) : S with type in_body := T.in_body and type out_body := T.out_body  = 
struct
  let name = T.name
      
  let transform (sm: T.in_body SailModule.t Logger.t) : T.out_body SailModule.t Logger.t = 
    let* sm = sm |> Logger.fail in 
    Logs.info (fun m -> m "Lowering module '%s' to '%s'" sm.md.name name);
    T.transform sm
end


type body_type = BMethod | BProcess


type 'a function_type = 
{
  name : string;
  body : 'a;
  ret : sailtype option;
  generics : string list;
  bt : body_type;
  pos : loc;
}


module MakeFunctionPass 
  (V : Env.Variable) 
  (T: 
    sig 
    val name : string 
    type in_body 
    type out_body 
    val lower_function : in_body function_type -> SailModule.SailEnv(V).t -> in_body SailModule.t -> out_body Logger.t 
    end)  
  : S with type in_body := T.in_body  and type out_body = T.out_body = 
struct
let name = T.name
type out_body = T.out_body

module VEnv = SailModule.SailEnv(V)

let lower_method (m:T.in_body method_defn) (sm : T.in_body SailModule.t) : T.out_body method_defn Logger.t = 
  let start_env = VEnv.get_start_env sm.declEnv m.m_proto.params in
  match m.m_body with
  | Right b -> 
    let decl = {
      name=m.m_proto.name;
      body=b;
      pos=m.m_proto.pos;
      ret=m.m_proto.rtype;
      bt=BMethod;
      generics=m.m_proto.generics
    } in
    let* e = start_env in
    let+ b = T.lower_function decl e sm in { m with m_body=Either.right b }
  | Left x ->  Logger.pure { m with m_body = Left x}


let lower_process (p: T.in_body process_defn) (sm : T.in_body SailModule.t) : T.out_body process_defn Logger.t  = 
  let start_env = VEnv.get_start_env sm.declEnv (fst p.p_interface) in
  let decl = {
      name=p.p_name;
      body=p.p_body;
      pos=p.p_pos;
      ret=None;
      bt=BProcess;
      generics=p.p_generics
  } in
  let* e = start_env in
  let+ p_body = T.lower_function decl e sm in
  { p with p_body}


let transform (sm :T.in_body SailModule.t Logger.t)  : T.out_body SailModule.t Logger.t =
  let* sm in
  Logs.info (fun m -> m "Lowering module '%s' to '%s'" sm.md.name name);
  (
  let+ methods = listMapM (fun methd -> lower_method methd sm) sm.methods |> Logger.recover ([])
  and* processes = listMapM (Fun.flip lower_process sm) sm.processes |> Logger.recover ([]) in

  { sm with
    processes;
    methods;
  }

  ) |> Logger.fail
end