open CodegenUtils
open CodegenEnv
open Common
open TypesCommon
open IrMir
open Monad.UseMonad(E)
module L = Llvm
module E = Error.Logger

let get_type (e:AstMir.expression) = snd e.info

let rec eval_l (env:SailEnv.t) (llvm:llvm_args) (x: AstMir.expression) : L.llvalue = 
  match x.exp with
  | Variable x -> let _,v = match (SailEnv.get_var x env) with Some (_,n) -> n | None -> failwith @@ Fmt.str "var '%s' not found" x |> snd in v
  | Deref x -> eval_r env llvm x
  | ArrayRead (array_exp, index_exp) -> 
    let array_val = eval_l env llvm array_exp in
    let index = eval_r env llvm index_exp in
    let llvm_array = L.build_in_bounds_gep array_val [|L.(const_int (i64_type llvm.c) 0 ); index|] "" llvm.b in 
    llvm_array
  | StructRead ((_,mname),struct_exp,(_,field)) -> 
    let st = eval_l env llvm struct_exp in
    let st_type_name = match snd struct_exp.info with CompoundType c -> snd c.name | _ -> failwith "problem with structure type" in 
    let fields = (SailEnv.get_decl st_type_name (Specific (mname,Struct)) env |> Option.get).defn.fields  in
    let _,_,idx = List.assoc field fields in 
    L.build_struct_gep st idx "" llvm.b
  
  | StructAlloc (_,(_,name),fields) -> 
    let _,fieldlist = fields |> List.split in
    let strct_ty = match L.type_by_name llvm.m ("struct." ^ name) with
    | Some s -> s
    | None -> "unknown structure : " ^ ("struct." ^ name) |> failwith 
    in
    let struct_v = L.build_alloca strct_ty "" llvm.b in 
    List.iteri ( fun i f ->
      let v = eval_r env llvm f in
      let v_f = L.build_struct_gep struct_v i "" llvm.b in
      L.build_store v v_f llvm.b |> ignore
      ) fieldlist; 
    struct_v

  | _ -> failwith "unexpected rvalue for codegen"


and eval_r (env:SailEnv.t) (llvm:llvm_args) (x:AstMir.expression) : L.llvalue = 
  let ty = get_type x in
  match x.exp with
  | Variable _ | StructRead _ | ArrayRead _ | StructAlloc _ ->  let v = eval_l env llvm x in L.build_load v "" llvm.b

  | Literal l -> getLLVMLiteral l llvm
  | UnOp (op,e) -> let l = eval_r env llvm e in unary op (ty_of_alias ty (snd env),l) llvm.b
  | BinOp (op,e1, e2) -> 
      let l1 = eval_r env llvm e1
      and l2 = eval_r env llvm e2
      in binary op (ty_of_alias ty (snd env)) l1 l2 llvm.b  
  | Ref (_,e) -> eval_l env llvm e
  | Deref e -> let v = eval_l env llvm e in L.build_load v "" llvm.b
  | ArrayStatic elements -> 
    begin
    let array_values = List.map (eval_r env llvm) elements in
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

  | EnumAlloc _ -> failwith "enum allocation unimplemented"

  | _ -> failwith "problem with thir"

and construct_call (name:string) ((_,mname):l_str) (args:AstMir.expression list) (env:SailEnv.t) (llvm:llvm_args) : L.llvalue = 
  let args_type,llargs = List.map (fun arg -> get_type arg,eval_r env llvm arg) args |> List.split
  in
  (* let mname = mangle_method_name name origin.mname args_type in  *)
  let mangled_name = "_" ^ mname ^ "_" ^ name in 
  Logs.debug (fun m -> m "constructing call to %s" name);
  let llval,ext = match SailEnv.get_decl mangled_name (Specific (mname,Method)) env with 
    | None ->   
      begin
      match SailEnv.get_decl name (Specific (mname,Method)) env with 
      | Some {llval;extern;_} -> llval,extern
      | None ->  Printf.sprintf "implementation of %s not found" mangled_name |> failwith
      end
    | Some {llval;extern;_} -> llval,extern 
  in

  let args = 
    if ext then 
      List.map2 (fun t v -> 
      let builder =
        match ty_of_alias t (snd env) with
        | Bool | Int _ | Char -> L.build_zext
        | Float -> L.build_bitcast
        | CompoundType _ -> fun v _ _ _ -> v
        | _ -> L.build_ptrtoint
        in
      builder v (L.i64_type llvm.c) "" llvm.b
    ) args_type llargs
    else 
      llargs 
  in
  L.build_call llval (Array.of_list args) "" llvm.b
  
open AstMir
  
let cfgToIR (proto:L.llvalue) (decls,cfg: mir_function) (llvm:llvm_args) (env :SailEnv.t) : unit = 
  let declare_var (mut:bool) (name:string) (ty:sailtype) (exp:AstMir.expression option) (env:SailEnv.t) : SailEnv.t E.t=
  let _ = mut in (* todo manage mutable types *)
    let entry_b = L.(entry_block proto |> instr_begin |> builder_at llvm.c) in
    let v =  
      match exp with
      | Some e -> 
          let t = get_type e 
          and v = eval_r env llvm e in
          let x = L.build_alloca (getLLVMType (snd env) t llvm.c llvm.m) name entry_b in 
          L.build_store v x llvm.b |> ignore; x  
      | None ->
        let t' = getLLVMType (snd env) ty llvm.c llvm.m in
        L.build_alloca t' name entry_b
    in
    SailEnv.declare_var name (dummy_pos,(mut,v)) env

  and assign_var (target:expression) (exp:expression) (env:SailEnv.t) = 
    let lvalue = eval_l env llvm target in
    let rvalue = eval_r env llvm exp in 
    L.build_store rvalue lvalue llvm.b |> ignore
    in

  let rec aux (lbl:label) (llvm_bbs : L.llbasicblock BlockMap.t) (env:SailEnv.t) : L.llbasicblock BlockMap.t = 
    if BlockMap.mem lbl llvm_bbs then llvm_bbs (* already treated, nothing to do *)
    else
      begin
        let bb = BlockMap.find lbl cfg.blocks
        and bb_name = (Printf.sprintf "lbl%i" lbl) in
        let llvm_bb = L.append_block llvm.c bb_name proto in
        let llvm_bbs = BlockMap.add lbl llvm_bb llvm_bbs in
        L.position_at_end llvm_bb llvm.b;
        List.iter (fun x -> assign_var x.target x.expression env) bb.assignments;
        match bb.terminator with
        | Some (Return e) ->  
            let ret = match e with
              | Some r ->  let v = eval_r env llvm r in L.build_ret v
              | None ->  L.build_ret_void
            in ret llvm.b |> ignore; llvm_bbs

        | Some (Goto lbl) -> 
          let llvm_bbs = aux lbl llvm_bbs env in
          L.position_at_end llvm_bb llvm.b;
          L.build_br (BlockMap.find lbl llvm_bbs) llvm.b |> ignore;
          llvm_bbs
          

        | Some (Invoke f) ->    
          let c = construct_call  f.id f.origin f.params env llvm  in
          begin
            match f.target with
            | Some id -> L.build_store c (let _,v = SailEnv.get_var id env |> Option.get |> snd in v) llvm.b |> ignore
            | None -> ()
          end;
          let llvm_bbs = aux f.next llvm_bbs env in
          L.position_at_end llvm_bb llvm.b;
          L.build_br (BlockMap.find f.next llvm_bbs) llvm.b |> ignore;
          llvm_bbs
        | Some (SwitchInt si) -> 
            let sw_val = eval_r env llvm si.choice in
            let sw_val = L.build_intcast sw_val (L.i32_type llvm.c) "" llvm.b (* for condition, expression val will be bool *)
            and llvm_bbs = aux si.default llvm_bbs env in
            L.position_at_end llvm_bb llvm.b;
            let sw = L.build_switch sw_val (BlockMap.find si.default llvm_bbs) (List.length si.paths) llvm.b in
            List.fold_left (
              fun bm (n,lbl) -> 
                let n = L.const_int (L.i32_type llvm.c) n 
                and bm = aux lbl bm env 
                in L.add_case sw n (BlockMap.find lbl bm);
                bm
            ) llvm_bbs si.paths

        | None -> failwith "no terminator : mir is broken" (* can't happen *)
        | Some Break -> failwith "no break should be there"
      end
  in
  (
    let+ env = ListM.fold_left (fun e (d:declaration) -> declare_var d.mut d.id d.varType None e) env decls
    in
    let init_bb = L.insertion_block llvm.b
    and llvm_bbs = aux cfg.input BlockMap.empty env in
    L.position_at_end init_bb llvm.b;
    L.build_br (BlockMap.find cfg.input llvm_bbs) llvm.b
  ) |> ignore

let methodToIR (llc:L.llcontext) (llm:L.llmodule) (decl:Declarations.method_decl) (env:SailEnv.t) (name : string) : L.llvalue =
  match Either.find_right decl.defn.m_body with 
  | None -> decl.llval (* extern method *)
  | Some b -> 
    Logs.info (fun m -> m "codegen of %s" name);
    let builder = L.builder llc in
    let llvm = {b=builder; c=llc ; m = llm; layout=Llvm_target.DataLayout.of_string (L.data_layout llm)} in

    if L.block_begin decl.llval <> At_end decl.llval then failwith ("redefinition of function " ^  name);

    let bb = L.append_block llvm.c "" decl.llval in
    L.position_at_end bb llvm.b;

    let args = toLLVMArgs decl.defn.m_proto.params (snd env) llvm in

    let new_env,args = Array.fold_left_map (
      fun env (m,_,v) -> 
        (
        let* env in 
        let+ new_env = SailEnv.declare_var (L.value_name v) (dummy_pos,(m,v)) env in 
        new_env
        ),v
      ) (E.pure env) args 

    in Array.iteri (fun i arg -> L.build_store (L.param decl.llval i) arg llvm.b |> ignore ) args;
    (let+ new_env in cfgToIR decl.llval b llvm new_env) |> ignore;
    decl.llval

let moduleToIR (sm: in_body SailModule.t) (verify_ir:bool) : L.llmodule E.t =
  let llc = L.create_context () in
  let llm = L.create_module llc sm.md.name in
  let* decls = get_declarations sm llc llm in
  let env = SailEnv.empty decls in

  DeclEnv.iter_decls (fun name m -> let func = methodToIR llc llm m env name in if verify_ir then Llvm_analysis.assert_valid_function func) (Self Method) decls >>= fun () ->
  if verify_ir then 
    match Llvm_analysis.verify_module llm with 
    | None -> return llm 
    | Some reason -> E.throw @@ Error.make dummy_pos (Fmt.str "LLVM : %s" reason)
  else return llm
    