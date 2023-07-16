open Llvm
open Common
open TypesCommon
open Env
module E = Error.Logger

open Monad.UseMonad(E)
open MakeOrderedFunctions(ImportCmp)

module Declarations = struct
  include SailModule.Declarations
  type process_decl = unit
  type method_decl = {defn : IrMir.Mir.Pass.out_body method_defn ; llval :  llvalue ; extern : bool}
  type struct_decl = {defn : struct_proto; ty : lltype}
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

open Declarations


  
let getLLVMBasicType f t llc llm  : lltype = 
  let rec aux = function
  | Bool -> i1_type llc
  | Int n -> integer_type llc n
  | Float -> double_type llc
  | Char -> i8_type llc
  | String -> i8_type llc |> pointer_type
  | ArrayType (t,s) -> array_type (aux t) s
  | Box t | RefType (t,_) -> aux t |> pointer_type
  | GenericType _ -> failwith "there should be no generic type, was degenerifyType used ? " 
  | CompoundType {name=(_,name); _} when name = "_value" -> i64_type llc (* for extern functions *)
  | CompoundType {origin=None;_} | CompoundType {decl_ty=None;_} -> failwith "compound type with no origin or decl_ty"
  | CompoundType  {origin=Some (_,mname); name=(_,name); decl_ty=Some d;_} -> 
    f (mname,name,d) llc llm aux
  in aux t


  let handle_compound_type_codegen env (mname,name,d) llc _llm aux : lltype = 
    match DeclEnv.find_decl name (Specific (mname,Filter [d])) env with 
    | Some (T tdef) -> 
      begin
        match tdef with
        | {ty=Some t;_} -> aux t 
        | {ty=None;_} -> i64_type llc
      end
    | Some (E _enum) -> failwith "todo enum"
    | Some (S {ty;_}) -> ty
    | Some _ -> failwith "something is broken"
    | None -> failwith @@ Fmt.str "getLLVMType : %s '%s' not found in module '%s'" (string_of_decl d) name mname


  let getLLVMType = fun e -> getLLVMBasicType (handle_compound_type_codegen e)

  let handle_compound_type env (mname,name,d) llc llm aux : lltype = 
    match SailModule.DeclEnv.find_decl name (Specific (mname,Filter [d])) env with 
    | Some (T tdef) -> 
      begin
        match tdef with
        | {ty=Some t;_} -> aux t 
        | {ty=None;_} -> i64_type llc
      end
    | Some (E _enum) -> failwith "todo enum"
    | Some (S (_,defn)) ->
      let _,f_types = List.split defn.fields in
      let elts = List.map (fun (_,t,_) -> aux t) f_types |> Array.of_list in
      begin
      match type_by_name llm ("struct." ^ name) with 
        | Some ty -> ty 
        | None -> (let ty = named_struct_type llc ("struct." ^ name) in
             struct_set_body ty elts false; ty)
      end
    | Some _ -> failwith "something is broken"
    | None -> failwith @@ Fmt.str "getLLVMType : %s '%s' not found in module '%s'" (string_of_decl d) name mname


  let _getLLVMType = fun e -> getLLVMBasicType (handle_compound_type e)

let llvm_proto_of_method_sig (m:method_sig) env llc llm = 
  let llvm_rt = match m.rtype with
  | Some t -> getLLVMType env t llc llm
  | None -> void_type llc
  in
  let args_type = List.map (fun ({ty;_}: param) -> getLLVMType env ty llc llm) m.params |> Array.of_list in
  let method_t = if m.variadic then var_arg_function_type else function_type in
  declare_function m.name (method_t llvm_rt args_type ) llm


let get_declarations (sm: IrMir.Mir.Pass.out_body SailModule.t) llc llm : DeclEnv.t E.t = 
  let open Monad.MonadSyntax(E) in
  let open Monad.MonadOperator(E) in

  Logs.debug (fun m -> m 
  "codegen of %i method(s), %i struct(s), %i type(s) and %i enum(s)"
   (List.length sm.methods)
    SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Struct |> container_length)
    SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Type |> container_length)
    SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Enum |> container_length)
  );

  let valueify_method_sig (m:method_sig) : method_sig =
    let open Monad.MonadOperator(MonadOption.M) in
    let value = fun pos -> CompoundType{origin=None;name=(pos,"_value");generic_instances=[];decl_ty=None} in
    let rtype = m.rtype in (* keep the current type *)
    let params = List.map (fun (p:param) -> {p with ty=(value p.loc)}) m.params in
    {m with params; rtype}
  in

  (* because the imports are at the mir stage, we also have to do some codegen for them *)

  let load_methods methods is_import env = 
    ListM.fold_left ( fun d m -> 
      let extern,proto = 
        if (Either.is_left m.m_body) then (* extern method, all parameters must be of type value *)
          true,valueify_method_sig m.m_proto
        else
          false,m.m_proto
        in
      let llproto = llvm_proto_of_method_sig proto env llc llm 
      in        
      let m_body = 
        if is_import then 
          Either.left (m.m_proto.name,[])  (* decls body from imports are opaque *)
        else m.m_body 
      in
      DeclEnv.add_decl m.m_proto.name {extern; defn = {m with m_body}; llval=llproto} Method d
    ) env methods
  in

  let module SEnv = MakeFromSequencable(SailModule.DeclEnv.StructSeq) in 
  let module TEnv = MakeFromSequencable(SailModule.DeclEnv.TypeSeq) in

  let load_types (sm: 'a SailModule.t) env = 
    TEnv.fold (fun acc (id,d) -> DeclEnv.add_decl id d Type acc) 
    env 
    SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Type)  
  in

  let load_structs (sm: 'a SailModule.t) write_env =  
    SEnv.fold (fun acc (name,(_,defn)) -> 
      let _,f_types = List.split defn.fields in
      let elts = List.map (fun (_,t,_) -> _getLLVMType sm.declEnv t llc llm) f_types |> Array.of_list in
      let ty = match type_by_name llm ("struct." ^ name) with 
        | Some ty -> ty 
        | None -> let ty = named_struct_type llc ("struct." ^ name) in
                  struct_set_body ty elts false; ty
    in
      DeclEnv.add_decl name {defn;ty} Struct acc
    ) 
    write_env
    SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Struct)
  in 
  let sorted_imports = (sm.imports |> ImportSet.elements |> List.sort (fun i1 i2 -> Int.compare i1.proc_order i2.proc_order)) in 

  Logs.debug (fun m -> m "import processing order : %s" (List.map (fun (i:import) -> Fmt.str "% i:%s" i.proc_order i.mname) sorted_imports |> String.concat " " ));
  
  let* decls = 
    ListM.fold_left (fun (e:DeclEnv.t) (i:import)  -> 
      Logs.debug (fun m -> m "processing import %s" i.mname);
      let (sm: 'a SailModule.t) = 
        In_channel.with_open_bin (i.dir ^ i.mname ^ Constants.mir_file_ext) Marshal.from_channel
      in
      (* putting import methods,types,structs and enums into mir env *)
      let empty_env = DeclEnv.(empty |> set_name i.mname |> replace_imports_with e) in
      let+ import_env = load_types sm empty_env >>= load_structs sm >>= load_methods sm.methods true in
      (* Logs.debug (fun m -> m "import %s env : %s"  i.mname @@ DeclEnv.string_of_env import_env); *)
      DeclEnv.add_import_decls (i,import_env) e 
    ) DeclEnv.(empty |> set_name sm.md.name) sorted_imports
  in  
  (* convert own decls, only after loading imports *)
  load_types sm decls >>= load_structs sm >>= load_methods sm.methods false
