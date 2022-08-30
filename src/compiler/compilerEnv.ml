open Llvm
open Common.TypesCommon
open Common.Env
open CompilerCommon


module Declarations = struct
  type process_decl = unit
  type method_decl = IrMir.Mir.Pass.out_body method_defn * llvalue
  type struct_decl = unit
  type enum_decl = unit
end

module DeclEnv = DeclarationsEnv (Declarations)

module SailEnv = VariableDeclEnv (Declarations)(
  struct 
    type t = bool * llvalue
    let string_of_var _ = ""

    let to_var _ (mut:bool) _ = mut,global_context () |> i1_type |> const_null (*fixme : make specialized var env for passes to not have this ugly thing *)

  end
) 

let get_declarations (sm: IrMir.Mir.Pass.out_body Common.SailModule.t) llc llm : DeclEnv.t = 
  Logs.debug (fun m -> m "generating %i llvm functions" (List.length sm.methods));
  
  List.fold_left ( fun d m -> 
    let proto = llvm_proto_of_method_sig m.m_proto llc llm in
    DeclEnv.add_method d m.m_proto.name (m,proto)
  ) DeclEnv.empty sm.methods
  (* todo : enums & structs *)





