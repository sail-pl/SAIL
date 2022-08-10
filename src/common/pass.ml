open Error
open Monad
open MonadFunctions(MonadError)
open MonadSyntax(MonadError)
open TypesCommon


module type ModulePass = sig

  type in_body
  type out_body  

  val lower : in_body SailModule.t -> out_body SailModule.t result
end


module type S = sig
  type in_body
  type out_body

  val lower : in_body SailModule.t result -> out_body SailModule.t result
end



module Make (T: ModulePass) : S with type in_body = T.in_body and type out_body = T.out_body = 
struct
  
  type in_body = T.in_body
  type out_body = T.out_body
      

  let lower (m: T.in_body SailModule.t result) : T.out_body SailModule.t result = 
    let* m in T.lower m
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


module MakeFunctionPass (V : Env.Variable) (T: sig type in_body type out_body val lower_function : in_body function_type -> SailModule.SailEnv(V).t -> out_body result end)   : S with type in_body = T.in_body  and type out_body = T.out_body  = 
struct

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
    let+ b = T.lower_function decl start_env in { m with m_body=Either.right b }
  | Left x ->  MonadError.pure { m with m_body = Left x}


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
  let+ p_body = T.lower_function decl start_env in
  { p with p_body}


let lower (m :T.in_body SailModule.t result)  : T.out_body SailModule.t result =
  let* m in
  let+ methods = listMapM (Fun.flip lower_method m.declEnv) m.methods 
  and* processes = listMapM (Fun.flip lower_process m.declEnv) m.processes  in
  { m with
    processes;
    methods;
  }


end