open Llvm
open CompilerCommon
open Common.TypesCommon

(* todo: simplify *)

type external_call = (method_sig * (llvalue array -> llvm_args ->  llvalue * llvalue array) option) list
let decl_printf (c:llcontext) : (llmodule -> llvalue)  =
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


let register_external name call ret args generics ext_l  : sailor_external string_assoc  = 
  let args = List.mapi (fun i t -> (string_of_int i,t)) args  in
  let decl : sailor_decl = {ret;args} in
  (name,{call;decl;generics})::ext_l


let convert_ffi f : string * sailor_external= 
  let generics=f.generics and name = f.name and ret = f.rtype and args = f.params in
  
  let call args llvm =
    let args_type = List.map (fun (_,t) -> getLLVMType t llvm.c llvm.m) f.params |> Array.of_list in
    let proto_ret = match ret with | None -> void_type llvm.c | Some t -> getLLVMType t llvm.c llvm.m in
    let proto = function_type proto_ret args_type in
    (declare_function f.name proto llvm.m, args)
  
  in
  (name, {call; generics; decl={ret;args}})


let inject_externals (ffi:method_sig list) : sailor_external string_assoc  =
  List.map convert_ffi ffi
  |> register_external "print_int" _print_int None [Int] []
  |> register_external "print_newline" _print_newline None [] []
  |> register_external "print_string" _print_string None [String] []
    (* printf but only 2 args (no support for varargs) *)
  |> register_external "printf" printf None [String; GenericType "T"] ["T"]

let find_ffi (name : string) (args : llvalue array) (llvm:llvm_args) (exts:sailor_external string_assoc) : sailtype option * llvalue =
  match List.assoc_opt name exts with
  | Some {call; decl;_} -> 
    let methd,args = call args llvm in
    decl.ret,build_call methd args "" llvm.b
  | _ -> failwith ("unknown external method " ^ name)


