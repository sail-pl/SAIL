open Expressions_gen
open Compiler_common
open Sail_env
open Llvm

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


  
let statementToIR (m:llvalue) (x: Ast.statement) (generics: sailor_args) (llvm:llvm_args) (env :SailEnv.t) : unit =
  let declare_var (mut:bool) (name:string) (ty:Common.sailtype) (exp:Ast.expression option) (env:SailEnv.t) : SailEnv.t =
    let _ = mut in (* todo manage mutable types *)
    let ty = degenerifyType ty generics in
    let var_type = getLLVMType ty llvm.c llvm.m  in
    let entry_b = entry_block m |> instr_begin |> builder_at llvm.c in
    let v =  
      match (ty,exp) with
      | (ArrayType _, Some e) -> 
        let _,array = eval_r env llvm e  in
        let array_alloc = build_alloca (type_of array) name entry_b in 
        build_store array array_alloc llvm.b |> ignore ; array_alloc
      | (ArrayType _,None) -> failwith "Error : array must have an initializer"   
      | (_, Some e) -> let x = build_alloca var_type name entry_b in 
          build_store (eval_r env llvm e |> snd) x llvm.b |> ignore; x  
      | _ -> build_alloca var_type name entry_b
    in
    Logs.debug (fun m -> m "declared %s with type %s " name (string_of_sailtype (Some ty))) ;
    SailEnv.declare_var env name (ty,v)
  in

  let rec aux x env : SailEnv.t = 
    match x with 
  | Ast.DeclVar (mut, name, t, exp) -> declare_var mut name t exp env 

  | DeclSignal _ -> failwith "unimplemented2"
  | Skip -> env
  | Assign (e1,e2) -> 
    let lvalue = eval_l env llvm e1 |> snd
    and rvalue = eval_r env llvm e2 |> snd in
    build_store rvalue lvalue llvm.b |> ignore;
    env

  | Seq (s1,s2)-> (* SailEnv.print_env env; *)  let new_env = aux s1 env in (* SailEnv.print_env new_env; *) aux s2 new_env

  | Par (_,_) ->  failwith "unimplemented6"

  | If (cond_exp, then_s, opt_else_s) -> 
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

  | While (e, s) -> 
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


  | Case (_,  _) ->  failwith "case unimplemented"

  | Invoke (_, name, args) -> construct_call name args env llvm eval_r |> ignore; env

  | Return opt_e -> 
    let current_bb = insertion_block llvm.b in
    if block_terminator current_bb |> Option.is_some then
      failwith "a return statement for the current block already exists !"
    else 
      let ret = match opt_e with
        | Some r ->  let v = eval_r env llvm r |> snd in build_ret v
        | None ->  build_ret_void
      in ret llvm.b |> ignore; env

  | Run (_, _) ->  failwith "run unimplemented"
  | Loop _ ->  failwith "loop unimplemented"
  | Emit _ ->  failwith "emit unimplemented"
  | Await _ ->  failwith "await unimplemented"
  | When (_, _) ->  failwith "when unimplemented"
  | Watching (_, _) -> failwith "watching unimplemented"
  | Block s -> 
    (* we create a new frame for inside the block and unstack it on return *)
    let new_env = aux s (SailEnv.new_frame env) in
    SailEnv.pop_frame new_env

in 
aux x env |> ignore
