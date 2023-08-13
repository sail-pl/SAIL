open Common
open TypesCommon
module E = Common.Error.Logger
open Monad.UseMonad(E)
open IrMir
open IrHir
open SailParser

type mono_body = {
  monomorphics : AstMir.mir_function method_defn list; 
  polymorphics : AstMir.mir_function method_defn list;
  processes : (HirUtils.statement,HirUtils.expression) AstParser.process_body process_defn list
}

module Pass = Pass.Make (struct
  let name = "Monomorphization"

  type in_body = (AstMir.mir_function,(HirUtils.statement,HirUtils.expression) AstParser.process_body) SailModule.methods_processes
  type out_body = mono_body

  module Env = SailModule.DeclEnv

  let transform (smdl : in_body SailModule.t) : out_body SailModule.t E.t =
    let polymorphics,monomorphics = List.partition (fun m -> m.m_proto.generics <> []) smdl.body.methods in
    return {smdl with body={monomorphics;polymorphics;processes=smdl.body.processes}}
end)