open Llvm
open Sail_env
open Compiler_common
open Common

(* todo: simplify *)

type exp_eval = SailEnv.t -> llvm_args -> Ast.expression -> llvalue
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


let register_external name bind ret args generics ext_l  : sailor_externals = 
  let args = List.mapi (fun i t -> (string_of_int i,t)) args  in
  let decl : sailor_decl = {ret;args} in
  (name,(decl,generics,bind))::ext_l


let get_externals () : sailor_externals =
  [] 
  |> register_external "print_int" _print_int None [Int] []
  |> register_external "print_newline" _print_newline None [] []
  |> register_external "print_string" _print_string None [String] []
  (* printf but only 2 args (no support for varargs) *)
  |> register_external "printf" printf None [String; GenericType "T"] ["T"]

let external_methods (name : string) (args : llvalue array) (llvm:llvm_args) (_env:SailEnv.t) : llvalue =
  match List.assoc_opt name (get_externals ()) with
  | Some (_,_,bind) -> 
    let methd,args = bind args llvm in
    build_call methd args "" llvm.b
  | _ -> failwith ("unknown external method " ^ name)


