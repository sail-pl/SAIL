open Llvm
open Common
open TypesCommon
open Env
module E = Error.Logger

open Monad.MonadFunctions(E)
open MakeOrderedFunctions(ImportCmp)
open Monad.MonadSyntax(E)

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

let getLLVMType (t : sailtype) (env:DeclEnv.t) (llc: llcontext)  (_llm: llmodule) : lltype = 
  let rec aux = function
  | Bool -> i1_type llc
  | Int -> i32_type llc 
  | Float -> double_type llc
  | Char -> i8_type llc
  | String -> i8_type llc |> pointer_type
  | ArrayType (t,s) -> array_type (aux t) s
  | CompoundType {name=(_,name); _} when name = "_value" -> i64_type llc (* for extern functions *)
  | CompoundType  {origin=Some (_,mname); name=(_,name); decl_ty=Some f;_} -> 
    (* only looking at type alias for now *)
    begin
    match DeclEnv.find_decl name (Specific (mname,Filter [f])) env with 
    | Some (T tdef) -> 
      begin
        match tdef with
        | {ty=Some t;_} -> aux t 
        | {ty=None;_} -> i64_type llc
      end
    | Some (E _enum) -> failwith "todo enum"
    | Some (S {ty;_}) -> ty
    | Some _ -> failwith "something is broken"
    | None -> failwith @@ Fmt.str "getLLVMType : type '%s' not found in %s" (string_of_sailtype (Some t)) mname

    end

  | Box t | RefType (t,_) -> aux t |> pointer_type
  | GenericType _ -> failwith "there should be no generic type, was degenerifyType used ? " 
  | CompoundType {origin=None;_} | CompoundType {decl_ty=None;_} -> failwith "compound type with no origin or decl_ty"
  in
  aux t

let llvm_proto_of_method_sig (m:method_sig) env llc llm = 
  let llvm_rt = match m.rtype with
  | Some t -> getLLVMType t env llc llm
  | None -> void_type llc
  in
  let args_type = List.map (fun ({ty;_}: param) -> getLLVMType ty env llc llm) m.params |> Array.of_list in
  let method_t = if m.variadic then var_arg_function_type else function_type in
  declare_function m.name (method_t llvm_rt args_type ) llm


let get_declarations (sm: IrMir.Mir.Pass.out_body SailModule.t) llc llm : DeclEnv.t E.t = 
  let open Monad.MonadSyntax(E) in

  Logs.debug (fun m -> m "generating %i llvm functions" (List.length sm.methods));

  let valueify_method_sig (m:method_sig) : method_sig =
    let open Monad.MonadOperator(MonadOption.M) in
    let value = fun pos -> CompoundType{origin=None;name=(pos,"_value");generic_instances=[];decl_ty=None} in
    let rtype = m.rtype in (* keep the current type *)
    let params = List.map (fun (p:param) -> {p with ty=(value p.loc)}) m.params in
    {m with params; rtype}
  in

  let methods_to_proto curr_env methods is_import = 
    ListM.fold_left ( fun d m -> 
      (* Logs.debug (fun x -> x "processing method %s is import : %b" m.m_proto.name is_import); *)
      let extern,proto = 
        if (Either.is_left m.m_body) then (* extern method, all parameters must be of type value *)
          true,valueify_method_sig m.m_proto
        else
          false,m.m_proto
        in
      let llproto = llvm_proto_of_method_sig proto curr_env llc llm 
      in        
      let m_body = 
        if is_import then 
          Either.left (m.m_proto.name,[])  (* decls body from imports are opaque *)
        else m.m_body 
      in
      DeclEnv.add_decl m.m_proto.name {extern; defn = {m with m_body}; llval=llproto} Method d
    ) curr_env methods
  in

  let module SEnv = MakeFromSequencable(SailModule.DeclEnv.StructSeq) in 
  let module TEnv = MakeFromSequencable(SailModule.DeclEnv.TypeSeq) in

  (* load types *)
  let* env = TEnv.fold (fun acc (id,d) -> DeclEnv.add_decl id d Type acc)  
          (DeclEnv.empty |> DeclEnv.set_name sm.md.name) 
            SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Type)  
  in

  (* load structs *)
  let* env = SEnv.fold (fun acc (name,(_,s)) -> 
    let _,f_types = List.split s.fields in
    let elts = List.map (fun (_,t,_) -> getLLVMType t env llc llm ) f_types |> Array.of_list in
    let struct_type =  name |> named_struct_type llc in
    struct_set_body struct_type elts false;
    DeclEnv.add_decl name {defn=s; ty=struct_type} Struct acc
    )  env SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Struct)
  in

  (* todo : enums *)

  let sorted_imports = (sm.imports |> ImportSet.elements |> List.sort (fun i1 i2 -> Int.compare i1.proc_order i2.proc_order)) in 

  (* Logs.debug (fun m -> m "import processing order : %s" (List.map (fun (i:import) -> Fmt.str "%i:%s" i.proc_order i.mname) sorted_imports |> String.concat " " )); *)
  let* decls = 
    ListM.fold_left  (fun (e:DeclEnv.t) (i:import)  -> 
      let (sm: 'a SailModule.t) = 
        In_channel.with_open_bin (i.dir ^ i.mname ^ Constants.mir_file_ext) Marshal.from_channel
      in
      (* putting import types into mir env *)
      let* e = TEnv.fold (fun accu (id,d)  -> DeclEnv.add_decl id d  Type accu) e  SailModule.DeclEnv.(get_own_decls sm.declEnv |> get_decls Type) in
      let e = DeclEnv.add_import_decls (i,e) e in 
      (* do the same for its methods *)
      methods_to_proto e sm.methods true
    ) env sorted_imports
  in

  (* Logs.debug (fun m -> m "%s" (DeclEnv.string_of_env decls)); *)
  
  (* convert own methods *)
  methods_to_proto decls sm.methods false




