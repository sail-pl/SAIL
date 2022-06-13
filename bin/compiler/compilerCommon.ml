open Llvm
open Common.TypesCommon
open Parser
open IrHir.AstHir

type llvm_args = { c:llcontext; b:llbuilder;m:llmodule; }

type 'a string_assoc = (string * 'a) list

type sailor_args = sailtype string_assoc

type sailor_decl = 
{
  ret : sailtype option;
	args : sailor_args;
}

type sailor_method = 
{
	decl : sailor_decl ;
	body: AstParser.expression statement;
  generics : sailor_args
}

type sailor_process = 
{
  args : sailor_args;
  body: AstParser.expression statement;
  generics : sailor_args
}

type function_type = FExternal | FMethod | FProcess

type sailor_function = 
{
  name : string;
  r_type : sailtype option;
  args : sailor_args;
  generics : string list;
  body : AstParser.expression statement option;
  ty : function_type
}

type sailor_functions = sailor_method FieldMap.t

type varTypesMap = sailtype FieldMap.t List.t (* List is used for scoping *)

type sailor_callables = {
  methodMap : sailor_method FieldMap.t;
  processMap : sailor_process FieldMap.t;
    (* todo : structs & enum *)
}

type sailor_external = {
  call : llvalue array -> llvm_args -> llvalue * llvalue array;
  decl : sailor_decl;
  generics : string list;
}


let mangle_method_name (name:string) (args: sailtype list ) : string =
  let back = List.fold_left (fun s t -> s ^ string_of_sailtype (Some t) ^ "_"  ) "" args in
  let front = "_" ^ name ^ "_" in
  let res = front ^ back in
  (* Logs.debug (fun m -> m "renamed %s to %s" name res); *)
  res


let degenerifyType (t: sailtype) (generics: sailor_args) : sailtype =
  let rec aux = function
  | Bool -> Bool
  | Int -> Int 
  | Float -> Float
  | Char -> Char
  | String -> String
  | ArrayType (t,s) -> ArrayType (aux t, s)
  | CompoundType (_name, _tl)-> failwith "todo compoundtype"
  | Box t -> Box (aux t) 
  | RefType (t,m) -> RefType (aux t, m)
  | GenericType t when generics = [] -> Printf.sprintf "generic type %s present but empty generics list" t |> failwith
  | GenericType n -> 
    begin
      match List.assoc_opt n generics with
      | Some t -> aux t
      | None -> Printf.sprintf "generic type %s not present in the generics list" n |> failwith
    end
  in
  aux t

let getLLVMType (t : sailtype) (llc: llcontext) (_llm: llmodule) : lltype = 
  let rec aux = function
  | Bool -> i1_type llc
  | Int -> i32_type llc 
  | Float -> double_type llc
  | Char -> i8_type llc
  | String -> i8_type llc |> pointer_type
  | ArrayType (t,s) -> array_type (aux t) s
  | CompoundType (_, [t])-> aux t
  | CompoundType _-> failwith "compound type unimplemented"
  | Box _ -> failwith "boxing unimplemented" 
  | RefType (t,_) -> aux t |> pointer_type
  | GenericType _ -> failwith "there should be no generic type, was degenerifyType used ? " 
  in
  aux t


let getLLVMLiteral (l:literal) (llvm:llvm_args) : llvalue =
  match l with
  | LBool b -> const_int (i1_type llvm.c) (Bool.to_int b)
  | LInt i -> const_int (i32_type llvm.c) i
  | LFloat f -> const_float (double_type llvm.c) f
  | LChar c -> const_int (i8_type llvm.c) (Char.code c)
  | LString s -> build_global_stringptr  s ".str" llvm.b


