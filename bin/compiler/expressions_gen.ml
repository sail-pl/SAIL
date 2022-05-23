open Common
open Compiler_common
open Sail_env
open Llvm
open Externals
open Saillib.Option
        
 

let unary (op:unOp) (l:llvalue) (_:llvm_args) : llvalue = 
  let ty = type_of l in
  let kind = classify_type ty in
  match kind,op with
  | Float,Neg ->const_fneg l
  | Integer,Neg -> const_neg l
  | _,Not  -> const_not l
  | _ -> Printf.sprintf "bad unary operand type : '%s'. Only double and int are supported" (string_of_lltype ty) |> failwith


let binary (op:binOp) (l1:llvalue) (l2:llvalue) (llvm:llvm_args) : llvalue = 
  if (type_of l1) <> (type_of l2) then
    failwith "operands are of different types !"
  else
    let ty = type_of l1 in
    let kind = classify_type ty in

    let operators = [
      (TypeKind.Integer, 
        [
          (Minus, build_sub) ; (Plus, build_add) ; (Rem, build_srem) ;
          (Mul,build_mul) ; (Div, build_sdiv) ; 
          (Eq, build_icmp Icmp.Eq) ; (NEq, build_icmp Icmp.Ne) ;
          (Lt, build_icmp Icmp.Slt) ; (Gt, build_icmp Icmp.Sgt) ; 
          (Le, build_icmp Icmp.Sle) ; (Ge, build_icmp Icmp.Sge) ;
          (And, build_and) ; (Or, build_or) ;
        ]
      ) ;
      (TypeKind.Double,
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

    let l = List.assoc_opt kind operators in
    let open MonadOption in
    match l >>| List.assoc op with
    | Some oper -> oper l1 l2 "" llvm.b
    | None ->  Printf.sprintf "bad binary operand type : '%s'. Only doubles and ints are supported" (string_of_lltype ty) |> failwith


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
