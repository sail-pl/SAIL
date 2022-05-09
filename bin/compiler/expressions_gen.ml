open Common
open Compiler_common
open Sail_env
open Llvm
open Externals
        
 

let unary (op:unOp) (l:llvalue) (_:llvm_args) : llvalue = 
  match op with
  | Neg when classify_value l = ConstantFP -> const_fneg l
  | Neg -> const_neg l
  | Not  -> const_not l


let binary (op:binOp) (l1:llvalue) (l2:llvalue) (llvm:llvm_args) : llvalue = 
  let oper = (match op with
  | Mul -> build_mul
  | Div -> build_sdiv
  | Eq -> build_icmp Icmp.Eq
  | NEq -> build_icmp Icmp.Ne
  | Lt -> build_icmp Icmp.Slt
  | Gt -> build_icmp Icmp.Sgt
  | Le -> build_icmp Icmp.Sle
  | Ge -> build_icmp Icmp.Sge
  | Or -> build_or
  | And -> build_and
  | Minus -> build_sub
  | Plus -> build_add
  | Rem -> build_srem
) in
oper l1 l2 "" llvm.b


let rec eval_l (env:SailEnv.t) (llvm:llvm_args) (x: Ast.expression) : llvalue = 
  let open Ast in
  match x with
  | Variable x -> SailEnv.get_var env x
  | Deref x-> eval_r env llvm x
  | ArrayRead (array_exp, index_exp) -> 
    let array = eval_l env llvm array_exp in
    let index = eval_r env llvm index_exp in
    build_gep array [|(const_int (i64_type llvm.c) 0); index|] "" llvm.b
  | StructRead _ -> failwith "struct assign unimplemented"
  | StructAlloc (_, _) -> failwith "struct allocation unimplemented"
  | EnumAlloc (_, _) -> failwith "enum allocation unimplemented"
  | ArrayStatic _ -> failwith "array alloc is not a lvalue"
  | Literal _ ->  failwith "literal is not a lvalue"
  | UnOp _ -> failwith "unary operator is not a lvalue"
  | BinOp _ -> failwith "binary operator is not a lvalue"
  | Ref _ -> failwith "reference read is not a lvalue"
  | MethodCall _ -> failwith "method call is not a lvalue"

and eval_r (env:SailEnv.t) (llvm:llvm_args) (x:Ast.expression) : llvalue = 
  match x with
  | Variable _ ->  let v = eval_l env llvm x in build_load v "" llvm.b
  | Literal c ->  getLLVMValue c llvm
  | UnOp (op,e) -> let l = eval_r env llvm e  in unary op l llvm
  | BinOp (op,e1, e2) -> 
      let l1 = eval_r env llvm e1
      and l2 = eval_r env llvm e2
      in binary op l1 l2 llvm
  | StructRead (_, _) -> failwith "struct read undefined"
  | ArrayRead _ -> let v = eval_l env llvm x in build_load v "" llvm.b
  | Ref (_,e) -> eval_l env llvm e
  | Deref e -> let l = eval_l env llvm e in build_load l "" llvm.b
  | ArrayStatic elements -> 
    begin
    let val_types = 
      (* the type of the array is the one of the first element *)
      List.hd elements |> eval_r env llvm |> type_of
    in 
    let array_type = array_type val_types (List.length elements) in 
    let array_values = List.map (eval_r env llvm) elements |> Array.of_list in

    (* all elements must have the same type *)
    if (not (Array.for_all (fun v -> type_of v = val_types) array_values)) then
      failwith "Error : mixed type array !";
  
    let array = const_array array_type array_values in
    build_load (define_global "const_array" array llvm.m) "" llvm.b
    end
  | StructAlloc _ -> failwith "struct alloc is not a rvalue"
  | EnumAlloc _   -> failwith "enum alloc is not a rvalue"
  | MethodCall (name, args) -> let args' = List.map (eval_r env llvm) args |> Array.of_list in
    begin
    match lookup_function name llvm.m with 
      | None -> external_methods eval_r name args llvm env
      | Some f -> build_call f args' "" llvm.b
    end
