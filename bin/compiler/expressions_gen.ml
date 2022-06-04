open Common
open Compiler_common
open Sail_env
open Llvm
open Externals
open Saillib.Option
        
 

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
    let open MonadOption in
    match l >>| List.assoc op with
    | Some oper -> oper l1 l2 ""
    | None ->  Printf.sprintf "bad binary operand type : '%s'. Only doubles and ints are supported" (string_of_sailtype (Some t)) |> failwith


let rec eval_l (env:SailEnv.t) (llvm:llvm_args) (x: Ast.expression)  : (sailtype * llvalue) = 
  let open Ast in
  match x with
  | Variable (_, x) -> SailEnv.get_var env x
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

and eval_r (env:SailEnv.t) (llvm:llvm_args) (x:Ast.expression) : (sailtype * llvalue) = 
  match x with
  | Variable _ ->  let t,v = eval_l env llvm x in t,build_load v "" llvm.b
  | Literal (_, l) ->  Type_checker.sailtype_of_literal l,getLLVMLiteral l llvm
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
  
  and construct_call (name:string) (args:Ast.expression list) (env:SailEnv.t) (llvm:llvm_args) : sailtype option * llvalue = 
    let args_type,args = List.map (eval_r env llvm) args |> List.split
    in
    let mname = mangle_method_name name args_type in 
    let args = Array.of_list args in
    match SailEnv.get_method env mname with 
    | None -> None,external_methods name args llvm env
    | Some {ret;proto} -> ret,build_call proto args "" llvm.b
    


