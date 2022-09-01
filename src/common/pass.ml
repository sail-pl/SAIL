open Error
open Monad
open TypesCommon

open MonadFunctions(Logger)
open MonadSyntax(Logger)
open MonadOperator(Logger)


module type ModulePass = sig
  val name : string
  type in_body
  type out_body  

  val lower : in_body SailModule.t -> out_body SailModule.t Logger.t
end


module type S = sig
  val name : string
  type in_body
  type out_body

  val lower : in_body SailModule.t Logger.t -> out_body SailModule.t Logger.t
end



module Make (T: ModulePass) : S with type in_body = T.in_body and type out_body = T.out_body = 
struct
  let name = T.name
  type in_body = T.in_body
  type out_body = T.out_body
      

  let lower (m: T.in_body SailModule.t Logger.t) : T.out_body SailModule.t Logger.t = 
    let* m = m |> Logger.fail in 
    Logs.info (fun m -> m "Lowering to '%s'" name);
    T.lower m 
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


module MakeFunctionPass (V : Env.Variable) (T: sig val name : string type in_body type out_body val lower_function : in_body function_type -> SailModule.SailEnv(V).t -> out_body Logger.t end)   : S with type in_body = T.in_body  and type out_body = T.out_body  = 
struct
let name = T.name
type in_body = T.in_body 
type out_body = T.out_body 

module VEnv = SailModule.SailEnv(V)

let lower_method (m:T.in_body method_defn) (decls : SailModule.DeclEnv.t)  = 
  let start_env = VEnv.get_start_env decls m.m_proto.params in
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
    let+ b = T.lower_function decl e in { m with m_body=Either.right b }
  | Left x ->  Logger.pure { m with m_body = Left x}


let lower_process (p: T.in_body process_defn) (decls : SailModule.DeclEnv.t)  = 
  let start_env = VEnv.get_start_env decls (fst p.p_interface) in
  let decl = {
      name=p.p_name;
      body=p.p_body;
      pos=p.p_pos;
      ret=None;
      bt=BProcess;
      generics=p.p_generics
  } in
  let* e = start_env in
  let+ p_body = T.lower_function decl e in
  { p with p_body}


let lower (m :T.in_body SailModule.t Logger.t)  : T.out_body SailModule.t Logger.t =
  let* m in
  Logs.info (fun m -> m "Lowering to '%s'" name);
  (
  let+ methods = listMapM (fun methd -> lower_method methd m.declEnv) m.methods |> Logger.recover ([])
  and* processes = listMapM (Fun.flip lower_process m.declEnv) m.processes |> Logger.recover ([]) in
  { m with
    processes;
    methods;
  }
  ) |> Logger.fail
end