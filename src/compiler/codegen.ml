open CompilerCommon
open Env
open Parser
open Common.TypesCommon
open Globals
open Llvm
open Externals
open IrHir


let unary (op:unOp) (t,v) : llvalue = 
  match t,op with
  | Float,Neg ->const_fneg v
  | Int,Neg -> const_neg v
  | _,Not  -> const_not v
  | _ -> Printf.sprintf "bad unary operand type : '%s'. Only double and int are supported" (string_of_sailtype (Some t)) |> failwith


let binary (op:binOp) (t:sailtype) (l1:llvalue) (l2:llvalue) : (llbuilder -> llvalue) = 
    let operators = [
      (Int, 
        [
          (Minus, build_sub) ; (Plus, build_add) ; (Rem, build_srem) ;
          (Mul,build_mul) ; (Div, build_sdiv) ; 
          (Eq, build_icmp Icmp.Eq) ; (NEq, build_icmp Icmp.Ne) ;
          (Lt, build_icmp Icmp.Slt) ; (Gt, build_icmp Icmp.Sgt) ; 
          (Le, build_icmp Icmp.Sle) ; (Ge, build_icmp Icmp.Sge) ;
          (And, build_and) ; (Or, build_or) ;
        ]
      ) ;
      (Float,
        [
          (Minus, build_fsub) ; (Plus, build_fadd) ; (Rem, build_frem) ;
          (Mul,build_fmul) ; (Div, build_fdiv) ; 
          (Eq, build_fcmp Fcmp.Oeq) ; (NEq, build_fcmp Fcmp.One) ;
          (Lt, build_fcmp Fcmp.Olt) ; (Gt, build_fcmp Fcmp.Ogt) ; 
          (Le, build_fcmp Fcmp.Ole) ; (Ge, build_fcmp Fcmp.Oge) ;
          (And, build_and) ; (Or, build_or) ;
        ]
      )
    ] in

    let l = List.assoc_opt t operators in
    let open Common.Option.MonadOption in
    match l >>| List.assoc op with
    | Some oper -> oper l1 l2 ""
    | None ->  Printf.sprintf "bad binary operand type : '%s'. Only doubles and ints are supported" (string_of_sailtype (Some t)) |> failwith


let rec eval_l (env:SailEnv.t) (llvm:llvm_args) (x: AstParser.expression)  : (sailtype * llvalue) = 
  let open AstParser in
  match x with
  | Variable (_, x) ->  SailEnv.get_var env x
  | Deref (_, x) -> eval_r env llvm x 
  | ArrayRead (_, array_exp, index_exp) -> 
    let array_t,array_val = eval_l env llvm array_exp in
    let t =
    match array_t with
    | ArrayType (t,_s) -> t
    | t ->  Printf.sprintf "typechecker is broken : 'array' type for %s is %s" (value_name array_val) (string_of_sailtype (Some t)) |> failwith
    in
    let _,index = eval_r env llvm index_exp  in
    let llvm_array = build_in_bounds_gep array_val [|(const_int (i64_type llvm.c) 0 ); index|] "" llvm.b in 
    RefType (t,true),llvm_array
  | StructRead _ -> failwith "struct assign unimplemented"
  | StructAlloc (_, _, _) -> failwith "struct allocation unimplemented"
  | EnumAlloc (_, _, _) -> failwith "enum allocation unimplemented"
  | ArrayStatic _ -> failwith "array alloc is not a lvalue"
  | Literal _ ->  failwith "literal is not a lvalue"
  | UnOp _ -> failwith "unary operator is not a lvalue"
  | BinOp _ -> failwith "binary operator is not a lvalue"
  | Ref _ -> failwith "reference read is not a lvalue"
  | MethodCall _ -> failwith "method call is not a lvalue"

and eval_r (env:SailEnv.t) (llvm:llvm_args) (x:AstParser.expression) : (sailtype * llvalue) = 
  match x with
  | Variable _ ->  let t,v = eval_l env llvm x in t,build_load v "" llvm.b
  | Literal (_, l) ->  TypeChecker.sailtype_of_literal l,getLLVMLiteral l llvm
  | UnOp (_, op,e) -> let t,l = eval_r env llvm e  in t,unary op (t,l)
  | BinOp (_, op,e1, e2) -> 
      let t,l1 = eval_r env llvm e1 
      and _,l2 = eval_r env llvm e2 
      in t,binary op t l1 l2 llvm.b
  | StructRead (_, _, _) -> failwith "struct read undefined"
  | ArrayRead _ -> let v_t,v = eval_l env llvm x in
    begin
    match v_t with
    | RefType (t,_) -> t,(build_load v "" llvm.b)
    | _ -> failwith "type system is broken"
    end
  
  | Ref (_, _,e) -> eval_l env llvm e 
  | Deref (_, e) -> 

    begin
      match eval_l env llvm e with
      | RefType (t,_),l -> t,build_load l "" llvm.b
      | _ -> failwith "type system is broken"
      end
  | ArrayStatic (_, elements) -> 
    begin
    let array_types,array_values = List.map (eval_r env llvm ) elements |> List.split in
    let ty = List.hd array_values |> type_of in
    let array_values = Array.of_list array_values in
    let array_type = array_type ty (List.length elements) in 
    let array = const_array array_type array_values in
    let array = define_global "const_array" array llvm.m in
    set_linkage Linkage.Private array;
    set_unnamed_addr true array;
    set_global_constant true array;
    (ArrayType (List.hd array_types, List.length elements)),build_load array "" llvm.b
    end
  | StructAlloc _ -> failwith "struct alloc is not a rvalue"
  | EnumAlloc _   -> failwith "enum alloc is not a rvalue"
  | MethodCall ( _, name, args) -> 
    let t,c = construct_call name args env llvm in
    (Option.get t),c
  
  and construct_call (name:string) (args:AstParser.expression list) (env:SailEnv.t) (llvm:llvm_args) : sailtype option * llvalue = 
    let args_type,args = List.map (eval_r env llvm) args |> List.split
    in
    let mname = mangle_method_name name args_type in 
    let args = Array.of_list args in
    Logs.info (fun m -> m "constructing call to %s with" mname);
    match SailEnv.get_function env mname with 
    | None -> 
      Logs.info (fun m -> m "function %s not found, searching externals..." mname);
      None,external_methods name args llvm env
    | Some {ret;proto} -> ret,build_call proto args "" llvm.b


  let rec block_returns (bb:llbasicblock) : bool = 
    match block_terminator bb with
    | Some s when instr_opcode s = Opcode.Ret ->  true
    | Some s when instr_opcode s = Opcode.Br ->  branch_returns s
    | _ -> false 
  and branch_returns (br:llvalue) : bool =
    match get_branch br with
    | Some `Conditional (_,then_bb, else_bb) ->  block_returns then_bb && block_returns else_bb
    | Some `Unconditional bb -> block_returns bb
    | None -> false
  
    
let statementToIR (m:llvalue) (x: AstParser.expression AstHir.statement) (generics: sailor_args) (llvm:llvm_args) (env :SailEnv.t) : unit =
  let declare_var (mut:bool) (name:string) (ty:sailtype) (exp:AstParser.expression option) (env:SailEnv.t) : SailEnv.t =
    let _ = mut in (* todo manage mutable types *)
    let ty = degenerifyType ty generics in
    let var_type = getLLVMType ty llvm.c llvm.m  in
    let entry_b = entry_block m |> instr_begin |> builder_at llvm.c in
    let v =  
      match (ty,exp) with
      | (_, Some e) -> let x = build_alloca var_type name entry_b in 
          build_store (eval_r env llvm e |> snd) x llvm.b |> ignore; x  
      | _ -> build_alloca var_type name entry_b
    in
    Logs.debug (fun m -> m "declared %s with type %s " name (string_of_sailtype (Some ty))) ;
    SailEnv.declare_var env name (ty,v)
  in

  let rec aux x env : SailEnv.t = 
    match x with 
  | AstHir.DeclVar (_, mut, name, t, exp) -> declare_var mut name t exp env 

  | DeclSignal _ -> failwith "unimplemented2"
  | Skip _ -> env
  | Assign (_, e1,e2) -> 
    let lvalue = eval_l env llvm e1 |> snd
    and rvalue = eval_r env llvm e2 |> snd in
    build_store rvalue lvalue llvm.b |> ignore;
    env

  | Seq (_, s1,s2)-> (* SailEnv.print_env env; *)  let new_env = aux s1 env in (* SailEnv.print_env new_env; *) aux s2 new_env

  | Par (_, _,_) ->  failwith "unimplemented6"

  | If (_, cond_exp, then_s, opt_else_s) -> 
    let cond = eval_r env llvm cond_exp |> snd
    and start_bb = insertion_block llvm.b  
    and then_bb = append_block llvm.c "then" m 
    and else_bb = append_block llvm.c "else" m
    and finally_bb = append_block llvm.c "finally" m
    in 
    let build_if_br s =
      aux s env |> ignore;
      (* br can change the current block *)
      let new_bb = insertion_block llvm.b in

      if (block_terminator new_bb |> Option.is_none ) then
        begin
        (* no block terminator means we must go to finally *)
        build_br finally_bb llvm.b |> ignore
        end;
    in
    position_at_end then_bb llvm.b;
    build_if_br then_s;
    position_at_end else_bb llvm.b;
    begin
      match opt_else_s with
      | None ->  build_br finally_bb llvm.b |> ignore
      | Some else_s -> build_if_br else_s
    end;

    position_at_end start_bb llvm.b;
    let if_br = build_cond_br cond then_bb else_bb llvm.b in
    position_at_end finally_bb llvm.b; 
    if branch_returns if_br then (    
      (* if both then & else branches return, finally will not be reached. 
          We must mark it as all blocks must have a terminator instruction *)   
      build_unreachable llvm.b |> ignore 
    ); env

  | While (_, e, s) -> 
      let start_bb = insertion_block llvm.b in
      let while_bb = append_block llvm.c "while" m in
      let do_bb = append_block  llvm.c "do" m in
      let finally_bb = append_block  llvm.c "finally" m in

      position_at_end start_bb llvm.b;
      build_br while_bb llvm.b |> ignore;

      position_at_end while_bb llvm.b;
      let cond = eval_r env llvm e |> snd in
      build_cond_br cond do_bb finally_bb llvm.b |> ignore;

      position_at_end do_bb llvm.b;
      let s_ret = aux s env in 
      build_br while_bb llvm.b |> ignore;
      position_at_end finally_bb llvm.b;
      s_ret
  | Case (_, _,  _) ->  failwith "case unimplemented"

  | Invoke (_, _, name, args) -> construct_call name args env llvm |> ignore; env

  | Return (_, opt_e) -> 
    let current_bb = insertion_block llvm.b in
    if block_terminator current_bb |> Option.is_some then
      failwith "a return statement for the current block already exists !"
    else 
      let ret = match opt_e with
        | Some r ->  let v = eval_r env llvm r |> snd in build_ret v
        | None ->  build_ret_void
      in ret llvm.b |> ignore; env

  | Run (_, _, _) ->  failwith "run unimplemented"
  | Emit _ ->  failwith "emit unimplemented"
  | Await _ ->  failwith "await unimplemented"
  | When (_, _, _) ->  failwith "when unimplemented"
  | Watching (_, _, _) -> failwith "watching unimplemented"
  | Block (_, s) -> 
    (* we create a new frame for inside the block and unstack it on return *)
    let new_env = aux s (SailEnv.new_frame env) in
    SailEnv.pop_frame new_env

in 
aux x env |> ignore
  


let toLLVMArgs (args: sailtype string_assoc ) (llvm:llvm_args) : (sailtype * llvalue) array = 
  let llvalue_list = List.map (
    fun (name, t) -> 
      let ty = getLLVMType t llvm.c llvm.m in 
      t,build_alloca ty name llvm.b
  ) args in
  Array.of_list llvalue_list

let methodToIR (llc:llcontext) (llm:llmodule) (env:SailEnv.t) (name : string) (m : sailor_method) : llvalue =
  let builder = builder llc in
  let llvm = {b=builder; c=llc ; m = llm} in
  
  let {proto;ret} = SailEnv.get_function env name |> Option.get in

  if block_begin proto <> At_end proto then
    failwith ("redefinition of function " ^  name);

  let bb = append_block llvm.c "" proto in
  position_at_end bb llvm.b;

  let args = toLLVMArgs m.decl.args llvm in

  let new_env,args = Array.fold_left_map (
    fun env tyvar -> 
      let new_env = SailEnv.declare_var env (value_name (snd tyvar)) tyvar in 
      (new_env, snd tyvar)
    ) env args 

  in Array.iteri (fun i arg -> build_store (param proto i) arg llvm.b |> ignore ) args;
  
  statementToIR proto m.body m.generics llvm new_env;

  begin
    match block_terminator (insertion_block llvm.b) with
    (* assuming the builder is on the last block of the method *)
    | Some _ -> ()
    (* allow not to have a return for void methods*)
    | None when ret = None -> build_ret_void llvm.b |> ignore
    (* there must always be a return if return type is not void *)
    | _ -> failwith "ERROR : method doesn't always return !"
  end;

  proto