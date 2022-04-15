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

let rec eval_l (x: Ast.expression) (env:SailEnv.t) (llvm:llvm_args) : llvalue = 
  let open Ast in
  match x with
  | Variable x -> SailEnv.get_var env x
  | Deref x-> eval_r x env llvm
  | ArrayRead (array_exp, index_exp) -> 
    let array = eval_l array_exp env llvm in
    let index = eval_r index_exp env llvm in
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



and eval_r (x: Ast.expression) (env:SailEnv.t) (llvm:llvm_args) : llvalue = 
  match x with
  | Variable _ ->  let v = eval_l x env llvm in build_load v "" llvm.b
  | Literal c ->  getLLVMValue c llvm
  | UnOp (op,e) -> let l = eval_r e env llvm  in unary op l llvm
  | BinOp (op,e1, e2) -> 
      let l1 = eval_r e1 env llvm 
      and l2 = eval_r e2 env llvm
      in binary op l1 l2 llvm
  | StructRead (_, _) -> failwith "struct read undefined"
  | ArrayRead _ -> let v = eval_l x env llvm in build_load v "" llvm.b
  | Ref (_,e) -> eval_l e env llvm
  | Deref e -> let l = eval_l e env llvm in build_load l "" llvm.b
  | ArrayStatic elements -> 
    begin
    let val_types = 
      (* the type of the array is the one of the first element *)
      eval_r (List.hd elements) env llvm |> type_of
    in 
    let array_type = array_type val_types (List.length elements) in 
    let array_values = llvalueArray_of_ExpList eval_r elements llvm env in

    (* all elements must have the same type *)
    if (not (Array.for_all (fun v -> type_of v = val_types) array_values)) then
      failwith "Error : mixed type array !";
  
    let array = const_array array_type array_values in
    build_load (define_global "const_array" array llvm.m) "" llvm.b
    end
  | StructAlloc _ -> failwith "struct alloc is not a rvalue"
  | EnumAlloc _   -> failwith "enum alloc is not a rvalue"
  | MethodCall (name, args) -> 
    begin
    match lookup_function name llvm.m with 
      | None -> external_methods eval_r name args llvm env
      | Some f -> build_call f (llvalueArray_of_ExpList eval_r args llvm env) "" llvm.b
    end
