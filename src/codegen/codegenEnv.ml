open Llvm
open Common
open TypesCommon
open Env
open CodegenCommon


module Declarations = struct
  type process_decl = unit
  type method_decl = IrMir.Mir.Pass.out_body method_defn * llvalue
  type struct_decl = unit
  type enum_decl = unit
  type type_decl = unit
end

module DeclEnv = DeclarationsEnv (Declarations)

module SailEnv = VariableDeclEnv (Declarations)(
  struct 
    type t = bool * llvalue
    let string_of_var _ = ""

    let to_var _ (mut:bool) _ = mut,global_context () |> i1_type |> const_null (*fixme : make specialized var env for passes to not have this ugly thing *)

  end
) 

let get_declarations (sm: IrMir.Mir.Pass.out_body SailModule.t) llc llm : DeclEnv.t = 
  Logs.debug (fun m -> m "generating %i llvm functions" (List.length sm.methods));

  
  let decl_to_proto curr_env methods ext = 
    List.fold_left ( fun d m -> 
      let proto = llvm_proto_of_method_sig m.m_proto llc llm in
      let m_body = if ext then Either.left (m.m_proto.name,None) else m.m_body in (* decls body from imports are opaque *)
      DeclEnv.add_decl d m.m_proto.name ({m with m_body},proto) Method
    ) curr_env methods
  in

  let menv = decl_to_proto DeclEnv.empty sm.methods false in 
  
  let decls = 
  ImportSet.fold (fun i e -> 
    let env = 
      In_channel.with_open_bin (i.dir ^ i.mname ^ ".mir") (fun f -> let imir : 'a SailModule.t =  Marshal.from_channel f in imir.methods) 
    in
    decl_to_proto e env true

  )  sm.imports menv  
  in
  (* DeclEnv.print_declarations decls; *) decls
  (* todo : enums & structs *)





