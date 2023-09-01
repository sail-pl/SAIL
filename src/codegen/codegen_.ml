open CodegenUtils
open CodegenEnv
open Common
open TypesCommon
open IrMir
open Monad.UseMonad(E)
module L = Llvm
module E = Logging.Logger
let get_type (e:MirAst.expression) = e.tag.ty

let rec eval_l (venv,tenv as env:SailEnv.t* Env.TypeEnv.t) (llvm:llvm_args) (exp: MirAst.expression) : L.llvalue E.t = 
  match exp.node with
  | Variable x -> 
    let+ _,v = match (SailEnv.get_var x venv) with 
      | Some (_,n) -> return n 
      | None -> E.throw Logging.(make_msg dummy_pos @@ Fmt.str "var '%s' not found" x)
    in v

  | Deref x -> eval_r env llvm x

  | ArrayRead a -> 
    let* array_val = eval_l env llvm a.array in
    let+ index = eval_r env llvm a.idx in
    let llvm_array = L.build_in_bounds_gep array_val [|L.(const_int (i64_type llvm.c) 0 ); index|] "" llvm.b in 
    llvm_array
    
  | StructRead2 s -> 
    let* st = eval_l env llvm s.value.strct in
    let* st_type_name = Env.TypeEnv.get_from_id (mk_locatable s.value.strct.tag.loc s.value.strct.tag.ty) tenv >>= function  
      | {value=CompoundType c;_} -> return c.name.value
      | _ -> E.throw Logging.(make_msg dummy_pos "problem with structure type") 
    in 
    let+ decl = (SailEnv.get_decl st_type_name (Specific (s.import.value,Struct)) venv 
                |> E.throw_if_none Logging.(make_msg exp.tag.loc @@ Fmt.str "compiler error : no decl '%s' found" st_type_name)) in

    let fields = decl.defn.fields in
    let {value=_,idx;_} = List.assoc s.value.field.value fields in 
    L.build_struct_gep st idx "" llvm.b
  
  | StructAlloc2 s -> 
    let _,fieldlist = s.value.fields |> List.split in
    let* strct_ty = match L.type_by_name llvm.m ("struct." ^ s.value.name.value) with
    | Some s -> return s
    | None -> 
      E.throw Logging.(make_msg exp.tag.loc  @@ "unknown structure : " ^ ("struct." ^ s.value.name.value))
    in
    let struct_v = L.build_alloca strct_ty "" llvm.b in 
    let+ () = ListM.iteri ( fun i f ->
      let+ v = eval_r env llvm f.value in
      let v_f = L.build_struct_gep struct_v i "" llvm.b in
      L.build_store v v_f llvm.b |> ignore
      ) fieldlist in
    struct_v

  | Literal _ | UnOp _ | BinOp _ |  Ref _ | ArrayStatic _  | EnumAlloc _ -> 
    E.throw Logging.(make_msg exp.tag.loc "unexpected lvalue for codegen")


and eval_r (venv,tenv as env:SailEnv.t* Env.TypeEnv.t) (llvm:llvm_args) (exp:MirAst.expression) : L.llvalue E.t = 
  let* ty = Env.TypeEnv.get_from_id (mk_locatable exp.tag.loc exp.tag.ty) tenv in
  match exp.node with
  | Variable _ | StructRead2 _ | ArrayRead _ | StructAlloc2 _ ->  let+ v = eval_l env llvm exp in L.build_load v "" llvm.b

  | Literal l -> return @@ getLLVMLiteral l llvm

  | UnOp (op,e) -> let+ l = eval_r env llvm e in unary op (let ty = ty_of_alias ty (snd venv) in (ty.loc,ty.value),l) llvm.b

  | BinOp bop -> 
      let+ l1 = eval_r env llvm bop.left
      and* l2 = eval_r env llvm bop.right
      in binary bop.op (ty_of_alias ty (snd venv)) l1 l2 llvm.b  
  | Ref (_,e) -> eval_l env llvm e

  | Deref e -> let+ v = eval_l env llvm e in L.build_load v "" llvm.b

  | ArrayStatic elements -> 
    begin
    let+ array_values = ListM.map (eval_r env llvm) elements in
    let ty = List.hd array_values |> L.type_of in
    let array_values = Array.of_list array_values in
    let array_type = L.array_type ty (List.length elements) in 
    let array = L.const_array array_type array_values in
    let array = L.define_global "const_array" array llvm.m in
    L.set_linkage L.Linkage.Private array;
    L.set_unnamed_addr true array;
    L.set_global_constant true array;
    L.build_load array "" llvm.b
    end

  | EnumAlloc _ -> E.throw Logging.(make_msg exp.tag.loc "enum allocation unimplemented") 


and construct_call (name:string) (mname:l_str) (args:MirAst.expression list) (venv,tenv as env : SailEnv.t*Env.TypeEnv.t) (llvm:llvm_args) : L.llvalue E.t = 
  let* args_type,llargs = ListM.map (fun arg -> let+ r = eval_r env llvm arg in arg.tag,r) args >>| List.split
  in
  (* let mname = mangle_method_name name origin.mname args_type in  *)
  let mangled_name = "_" ^ mname.value ^ "_" ^ name in 
  Logs.debug (fun m -> m "constructing call to %s" name);
  let* llval,ext = match SailEnv.get_decl mangled_name (Specific (mname.value,Method)) venv with 
    | None ->   
      begin
      match SailEnv.get_decl name (Specific (mname.value,Method)) venv with 
      | Some {llval;extern;_} -> return (llval,extern)
      | None -> E.throw Logging.(make_msg mname.loc @@ Printf.sprintf "implementation of %s not found" mangled_name ) 
      end
    | Some {llval;extern;_} -> return (llval,extern)
  in

  let+ args = 
    if ext then 
      ListM.map2 (fun (t:IrThir.ThirUtils.tag) v ->
      let+ t = Env.TypeEnv.get_from_id (mk_locatable t.loc t.ty) tenv in  
      let builder =
        match (ty_of_alias t (snd venv)).value with
        | Bool | Int _ | Char -> L.build_zext
        | Float -> L.build_bitcast
        | CompoundType _ -> fun v _ _ _ -> v
        | _ -> L.build_ptrtoint
      in
      builder v (L.i64_type llvm.c) "" llvm.b
    ) args_type llargs
    else 
      return llargs 
  in
  L.build_call llval (Array.of_list args) "" llvm.b
  
open MirAst
  
let cfgToIR (proto:L.llvalue) (decls,cfg: mir_function) (llvm:llvm_args) (venv,tenv : SailEnv.t*Env.TypeEnv.t) : unit E.t = 
  let declare_var (mut:bool) (name:string) (ty:sailtype) (exp:MirAst.expression option) (venv : SailEnv.t) : SailEnv.t E.t =
    let _ = mut in (* todo manage mutable types *)
      let entry_b = L.(entry_block proto |> instr_begin |> builder_at llvm.c) in
      let* v =  
        match exp with
        | Some e -> 
            let* t = Env.TypeEnv.get_from_id (mk_locatable e.tag.loc e.tag.ty) tenv 
            and* v = eval_r (venv,tenv) llvm e in
            let+ ty = getLLVMType (snd venv) t llvm.c llvm.m in
            let x = L.build_alloca ty name entry_b in 
            L.build_store v x llvm.b |> ignore; x  
        | None ->
          let+ t' = getLLVMType (snd venv) ty llvm.c llvm.m in
          L.build_alloca t' name entry_b
      in
      SailEnv.declare_var name (dummy_pos,(mut,v)) venv
  in
  let assign_var (target:expression) (exp:expression) (env : SailEnv.t*Env.TypeEnv.t) = 
    let* lvalue = eval_l env llvm target in
    let+ rvalue = eval_r env llvm exp in 
    L.build_store rvalue lvalue llvm.b |> ignore
  in

  let rec aux (lbl:label) (llvm_bbs : L.llbasicblock BlockMap.t) (venv : SailEnv.t) : L.llbasicblock BlockMap.t E.t = 
    if BlockMap.mem lbl llvm_bbs then return llvm_bbs (* already treated, nothing to do *)
    else
      begin
        let bb = BlockMap.find lbl cfg.blocks
        and bb_name = (Printf.sprintf "lbl%i" lbl) in
        let llvm_bb = L.append_block llvm.c bb_name proto in
        let llvm_bbs = BlockMap.add lbl llvm_bb llvm_bbs in
        L.position_at_end llvm_bb llvm.b;
        let* () = ListM.iter (fun x -> assign_var x.target x.expression (venv,tenv)) bb.assignments in
        let* terminator = E.throw_if_none Logging.(make_msg bb.location "no terminator : mir is broken") bb.terminator in
        match terminator with
        | Return e ->  
            let+ ret = match e with
              | Some r ->  let+ v = eval_r (venv,tenv) llvm r in L.build_ret v
              | None ->  return L.build_ret_void
            in ret llvm.b |> ignore; llvm_bbs

        | Goto lbl -> 
          let+ llvm_bbs = aux lbl llvm_bbs venv in
          L.position_at_end llvm_bb llvm.b;
          let _ = L.build_br (BlockMap.find lbl llvm_bbs) llvm.b in
          llvm_bbs

        | Invoke f ->  
          let* c = construct_call f.id f.origin f.params (venv,tenv) llvm  in
          begin
            match f.target with
            | Some id -> L.build_store c (let _,v = SailEnv.get_var id venv |> Option.get |> snd in v) llvm.b |> ignore
            | None -> ()
          end;
          let+ llvm_bbs = aux f.next llvm_bbs venv in
          L.position_at_end llvm_bb llvm.b;
          L.build_br (BlockMap.find f.next llvm_bbs) llvm.b |> ignore;
          llvm_bbs

        | SwitchInt si -> 
            let* sw_val = eval_r (venv,tenv) llvm si.choice in
            let sw_val = L.build_intcast sw_val (L.i32_type llvm.c) "" llvm.b in (* for condition, expression val will be bool *)
            let* llvm_bbs = aux si.default llvm_bbs venv in
            L.position_at_end llvm_bb llvm.b;
            let sw = L.build_switch sw_val (BlockMap.find si.default llvm_bbs) (List.length si.paths) llvm.b in
            ListM.fold_left (
              fun bm (n,lbl) -> 
                let n = L.const_int (L.i32_type llvm.c) n in
                let+ bm = aux lbl bm venv 
                in L.add_case sw n (BlockMap.find lbl bm);
                bm
            ) llvm_bbs si.paths
        | Break -> E.throw Logging.(make_msg bb.location "no break should be there") 
      end
  in
  (
    let* env = ListM.fold_left (fun e (d:declaration) -> declare_var d.mut d.id d.varType None e) venv decls
    in
    let init_bb = L.insertion_block llvm.b in
    let+ llvm_bbs = aux cfg.input BlockMap.empty env in
    L.position_at_end init_bb llvm.b;
    L.build_br (BlockMap.find cfg.input llvm_bbs) llvm.b |> ignore
  )

let methodToIR (llc:L.llcontext) (llm:L.llmodule) (decl:Declarations.method_decl) (venv,tenv:SailEnv.t * Env.TypeEnv.t) (name : string) : L.llvalue E.t =
  match Either.find_right decl.defn.m_body with 
  | None -> return decl.llval (* extern method *)
  | Some b -> 
    Logs.info (fun m -> m "codegen of %s" name);
    let builder = L.builder llc in
    let llvm = {b=builder; c=llc ; m = llm; layout=Llvm_target.DataLayout.of_string (L.data_layout llm)} in
    let* () = E.throw_if Logging.(make_msg dummy_pos @@ "redefinition of function " ^  name) (L.block_begin decl.llval <> At_end decl.llval) in
    let bb = L.append_block llvm.c "" decl.llval in
    L.position_at_end bb llvm.b;

    let* args = toLLVMArgs decl.defn.m_proto.params (snd venv) llvm in

    let new_env,args = Array.fold_left_map (
      fun env (m,_,v) -> 
        (
        let* env in 
        let+ new_env = SailEnv.declare_var (L.value_name v) (dummy_pos,(m,v)) env in 
        new_env
        ),v
      ) (E.pure venv) args 

    in Array.iteri (fun i arg -> L.build_store (L.param decl.llval i) arg llvm.b |> ignore ) args;
    let* new_env in 
    let+ () = cfgToIR decl.llval b llvm (new_env,tenv) in
    decl.llval

let moduleToIR (sm: in_body SailModule.t) (verify_ir:bool) : L.llmodule E.t =
  let llc = L.create_context () in
  let llm = L.create_module llc sm.md.name in
  let* decls = get_declarations sm llc llm in
  let env = SailEnv.empty decls,sm.typeEnv in
  let method_cg name m : unit E.t = 
    let+ m = methodToIR llc llm m env name in 
    if verify_ir then Llvm_analysis.assert_valid_function m                                      
  in 
  let* _ = DeclEnv.fold_decls (fun id m accu -> let r = method_cg id m in r::accu) [] Method decls |> ListM.sequence in    
  if verify_ir then 
    match Llvm_analysis.verify_module llm with 
    | None -> return llm 
    | Some reason -> E.throw Logging.(make_msg dummy_pos (Fmt.str "LLVM : %s" reason))
  else return llm
    