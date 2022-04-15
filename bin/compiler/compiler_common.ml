open Llvm
open Common
open Sail_env

type llvm_args = { c:llcontext; b:llbuilder;m:llmodule; }

type statement_return = SailEnv.t * ( SailEnv.value option )

let rec getLLVMType (t : sailtype) (c: llcontext) : lltype = 
  match t with
  | Bool -> i1_type c
  | Int -> i32_type c 
  | Float -> double_type c
  | Char -> i8_type c
  | String -> pointer_type (i8_type c)
  | ArrayType t -> getLLVMType t c (* we just return the type of the elements *)
  | CompoundType (_, [t])-> getLLVMType t c
  | CompoundType _-> failwith "compound type unimplemented"
  | Box _ -> failwith "boxing unimplemented"
  | RefType (t,_) -> getLLVMType t c |> pointer_type
  | GenericType _ -> failwith "generic types unimplemented"


let getLLVMValue (l:literal) (llvm:llvm_args) : llvalue =
  match l with
  | LBool b -> const_int (i1_type llvm.c) (Bool.to_int b)
  | LInt i -> const_int (i32_type llvm.c) i
  | LFloat f -> const_float (double_type llvm.c) f
  | LChar c -> const_int (i8_type llvm.c) (Char.code c)
  | LString s -> build_global_stringptr  s ".str" llvm.b