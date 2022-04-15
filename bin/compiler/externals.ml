open Llvm
open Sail_env
open Compiler_common

(* todo: simplify *)

type exp_eval = Ast.expression -> SailEnv.t -> llvm_args -> llvalue

let llvalueArray_of_ExpList (eval:exp_eval) (args: Ast.expression list) (llvm:llvm_args) (env:SailEnv.t) : llvalue array = 
  let llvalue_list = List.map (fun arg -> eval arg env llvm) args in
  Array.of_list llvalue_list

let decl_printf (c:llcontext) : (llmodule -> llvalue) =
  let proto = var_arg_function_type (i32_type c) [|pointer_type (i8_type c)|] in
  declare_function "printf" proto


let _print_string (args:llvalue array) (llvm:llvm_args) : llvalue  * llvalue array =
  let args =
   match Array.length args with
   | 1 -> args
  | n -> Printf.sprintf "print_string: takes 1 argument (%d given)" n |> failwith
  in (decl_printf llvm.c llvm.m, args)
   

let _print_int (args:llvalue array) (llvm:llvm_args) : llvalue  * llvalue array =
  let args =
  match args with
  | [|i|] ->  let fmt = build_global_stringptr "%d" ".str" llvm.b in
    [| fmt ; i|]
  | _ -> Printf.sprintf "print_int: takes 1 argument (%d given)" (Array.length args) |> failwith
  in (decl_printf llvm.c llvm.m, args)


let _print_newline (args:llvalue array) (llvm:llvm_args) : llvalue  * llvalue array =
  let args =
  match args with
  | [||] ->  let fmt = build_global_stringptr "\n" ".str" llvm.b in
    [| fmt |]
  | _ -> Printf.sprintf "print_newline takes 0 arguments (%d given)" (Array.length args) |> failwith
  in (decl_printf llvm.c llvm.m, args)


let printf  (args:llvalue array) (llvm:llvm_args) : llvalue  * llvalue array =
  decl_printf llvm.c llvm.m, args

  

let external_methods (eval:exp_eval) (name : string) (args : Ast.expression list) (llvm:llvm_args) (env:SailEnv.t) : llvalue =
  let args =  llvalueArray_of_ExpList eval args llvm env in
  let method_builder =
  match name with
  | "print_string" -> _print_string
  | "print_int" -> _print_int
  | "print_newline" -> _print_newline
  | "printf" -> printf
  | _ -> failwith ("unknown external method " ^ name)
  in 
  let methd,args = method_builder args llvm in
  build_call methd args "" llvm.b