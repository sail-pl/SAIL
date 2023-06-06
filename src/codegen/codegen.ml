open CodegenUtils
open CodegenEnv
open Common
open TypesCommon
open Llvm
open IrMir

module E = Error.Logger

open Common.Monad.MonadSyntax(E)
open Common.Monad.MonadFunctions(E)

let get_type (e:AstMir.expression) = snd e.info

let rec eval_l (env:SailEnv.t) (llvm:llvm_args) (x: AstMir.expression) : llvalue = 
  match x.exp with
  | Variable x -> let _,v = SailEnv.get_var x env |> Option.get |> snd in v
  | Deref x -> eval_r env llvm x
  | ArrayRead (array_exp, index_exp) -> 
    let array_val = eval_l env llvm array_exp in
    let index = eval_r env llvm index_exp in
    let llvm_array = build_in_bounds_gep array_val [|(const_int (i64_type llvm.c) 0 ); index|] "" llvm.b in 
    llvm_array
  | StructRead _ -> failwith "struct assign unimplemented"
  | StructAlloc _ -> failwith "struct allocation unimplemented"
  | EnumAlloc _ -> failwith "enum allocation unimplemented"
  | _  -> failwith "problem with thir"

and eval_r (env:SailEnv.t) (llvm:llvm_args) (x:AstMir.expression) : llvalue = 
  let ty = get_type x in
  match x.exp with
  | Variable _ ->  let v = eval_l env llvm x in build_load v "" llvm.b
  | Literal l ->  getLLVMLiteral l llvm
  | UnOp (op,e) -> let l = eval_r env llvm e in unary op (ty_of_compound_type ty (snd env),l) llvm.b
  | BinOp (op,e1, e2) -> 
      let l1 = eval_r env llvm e1
      and l2 = eval_r env llvm e2
      in binary op (ty_of_compound_type ty (snd env)) l1 l2 llvm.b
  | StructRead _ -> failwith "struct read undefined"
  | ArrayRead _ -> let v = eval_l env llvm x in build_load v "" llvm.b    
  | Ref (_,e) -> eval_l env llvm e
  | Deref e -> let v = eval_l env llvm e in build_load v "" llvm.b
  | ArrayStatic elements -> 
    begin
    let array_values = List.map (eval_r env llvm) elements in
    let ty = List.hd array_values |> type_of in
    let array_values = Array.of_list array_values in
    let array_type = array_type ty (List.length elements) in 
    let array = const_array array_type array_values in
    let array = define_global "const_array" array llvm.m in
    set_linkage Linkage.Private array;
    set_unnamed_addr true array;
    set_global_constant true array;
    build_load array "" llvm.b
    end
  | _ -> failwith "problem with thir"
and construct_call (name:string) (origin:import) (args:AstMir.expression list) (env:SailEnv.t) (llvm:llvm_args) : llvalue = 
  let args_type,llargs = List.map (fun arg -> get_type arg,eval_r env llvm arg) args |> List.split
  in
  (* let mname = mangle_method_name name origin.mname args_type in  *)
  let mname = "_" ^ origin.mname ^ "_" ^ name in 
  Logs.debug (fun m -> m "constructing call to %s" name);
  let llval,ext = match SailEnv.get_decl mname (Self Method) env with 
    | None ->   
      begin
      match SailEnv.get_decl name (Self Method) env with 
      | Some {llval;extern;_} -> llval,extern
      | None ->  Printf.sprintf "implementation of %s not found" name |> failwith
      end
    | Some {llval;extern;_} -> llval,extern 
  in

  let args = 
    if ext then 
      List.map2 (fun t v -> 
      let builder =
        match ty_of_compound_type t (snd env) with
        | Bool | Int | Char -> build_zext
        | Float -> build_bitcast
        | _ -> build_ptrtoint
        in
      builder v (i64_type llvm.c) "" llvm.b
    ) args_type llargs
    else 
      llargs 
  in
  build_call llval (Array.of_list args) "" llvm.b
  
open AstMir
  
let cfgToIR (proto:llvalue) (decls,cfg: Mir.Pass.out_body) (llvm:llvm_args) (env :SailEnv.t) : unit = 
  let declare_var (mut:bool) (name:string) (ty:sailtype) (exp:AstMir.expression option) (env:SailEnv.t) : SailEnv.t E.t=
    let _ = mut in (* todo manage mutable types *)
    let entry_b = entry_block proto |> instr_begin |> builder_at llvm.c in
    let v =  
      match exp with
      | Some e -> 
          let t = get_type e 
          and v = eval_r env llvm e in
          let x = build_alloca (getLLVMType t (snd env) llvm.c llvm.m) name entry_b in 
          build_store v x llvm.b |> ignore; x  
      | None ->
        let t' = getLLVMType ty (snd env) llvm.c llvm.m in
        build_alloca t' name entry_b
    in
    SailEnv.declare_var name  (dummy_pos,(mut,v)) env

  and assign_var (target:expression) (exp:expression) (env:SailEnv.t) = 
    let lvalue = eval_l env llvm target 
    and rvalue = eval_r env llvm exp in
    build_store rvalue lvalue llvm.b |> ignore
    in

  let rec aux (lbl:label) (llvm_bbs : llbasicblock BlockMap.t) (env:SailEnv.t) : llbasicblock BlockMap.t = 
    match BlockMap.find_opt lbl llvm_bbs with
    | None -> 
      begin
        let bb = BlockMap.find lbl cfg.blocks
        and bb_name = (Printf.sprintf "lbl%i" lbl) in
        let llvm_bb = append_block llvm.c bb_name proto in
        let llvm_bbs = BlockMap.add lbl llvm_bb llvm_bbs in
        position_at_end llvm_bb llvm.b;
        List.iter (fun x -> assign_var x.target x.expression env) bb.assignments;
        match bb.terminator with
        | Some (Return e) ->  
            let ret = match e with
              | Some r ->  let v = eval_r env llvm r in build_ret v
              | None ->  build_ret_void
            in ret llvm.b |> ignore; llvm_bbs

        | Some (Goto lbl) -> 
          let llvm_bbs = aux lbl llvm_bbs env in
          position_at_end llvm_bb llvm.b;
          build_br (BlockMap.find lbl llvm_bbs) llvm.b |> ignore;
          llvm_bbs
          

        | Some (Invoke f) ->    
          let c = construct_call  f.id f.origin f.params env llvm  in
          begin
            match f.target with
            | Some id -> build_store c (let _,v = SailEnv.get_var id env |> Option.get |> snd in v) llvm.b |> ignore
            | None -> ()
          end;
          let llvm_bbs = aux f.next llvm_bbs env in
          position_at_end llvm_bb llvm.b;
          build_br (BlockMap.find f.next llvm_bbs) llvm.b |> ignore;
          llvm_bbs
        | Some (SwitchInt (e,cases,default)) -> 
            let sw_val = eval_r env llvm e in
            let sw_val = build_intcast sw_val (i32_type llvm.c) "" llvm.b (* for condition, expression val will be bool *)
            and llvm_bbs = aux default llvm_bbs env in
            position_at_end llvm_bb llvm.b;
            let sw = build_switch sw_val (BlockMap.find default llvm_bbs) (List.length cases) llvm.b in
            List.fold_left (
              fun bm (n,lbl) -> 
                let n = const_int (i32_type llvm.c) n 
                and bm = aux lbl bm env 
                in add_case sw n (BlockMap.find lbl bm);
                bm
            ) llvm_bbs cases

        | None -> failwith "no terminator : mir is broken" (* can't happen *)
        | Some Break -> failwith "no break should be there"
      end

    | Some _ -> llvm_bbs (* already treated, nothing to do *)
  in
  (let+ env = ListM.fold_left (fun e (d:declaration) -> declare_var d.mut d.id d.varType None e) env decls
  in
  let init_bb = insertion_block llvm.b
  and llvm_bbs = aux cfg.input BlockMap.empty env in
  position_at_end init_bb llvm.b;
  build_br (BlockMap.find cfg.input llvm_bbs) llvm.b) |> ignore

let methodToIR (llc:llcontext) (llm:llmodule) (decl:Declarations.method_decl) (env:SailEnv.t) (name : string) : llvalue =
  match Either.find_right decl.defn.m_body with 
  | None -> decl.llval (* extern method *)
  | Some b -> 
    Logs.info (fun m -> m "codegen of %s" name);
    let builder = builder llc in
    let llvm = {b=builder; c=llc ; m = llm} in

    if block_begin decl.llval <> At_end decl.llval then failwith ("redefinition of function " ^  name);

    let bb = append_block llvm.c "" decl.llval in
    position_at_end bb llvm.b;

    let args = toLLVMArgs decl.defn.m_proto.params (snd env) llvm in

    let new_env,args = Array.fold_left_map (
      fun env (m,_,v) -> 
        (
        let* env in 
        let+ new_env = SailEnv.declare_var (value_name v) (dummy_pos,(m,v)) env in 
        new_env
        ),v
      ) (E.pure env) args 

    in Array.iteri (fun i arg -> build_store (param decl.llval i) arg llvm.b |> ignore ) args;
    (let+ new_env in cfgToIR decl.llval b llvm new_env) |> ignore;
    decl.llval

