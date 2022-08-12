open Llvm
open Common
open TypesCommon

type llvm_args = { c:llcontext; b:llbuilder;m:llmodule; }

type 'a string_assoc = (string * 'a) list

type sailor_args = sailtype string_assoc

type sailor_decl = 
{
  ret : sailtype option;
	args : sailor_args;
}


type varTypesMap = sailtype FieldMap.t List.t (* List is used for scoping *)


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

(* temporary pass, convert Main process into a method, throws error if not found or other processes exist *)

open Monad.MonadSyntax(Common.Error.MonadError)


  module Pass = Pass.Make( struct

  type in_body = IrMir.Mir.Pass.out_body
  type out_body  = in_body

  let method_of_main_process (p:in_body process_defn list) : out_body method_defn Error.result = 
    match List.find_opt (fun p -> p.p_name = "Main") p with
    | Some p -> 
      let m_proto = {pos=p.p_pos; name="main"; generics = p.p_generics; params = fst p.p_interface; variadic=false; rtype=None} 
      and m_body = Either.right p.p_body in
      {m_proto; m_body} |> Result.ok
    | None -> Result.error [dummy_pos, "no Main process found"]

  let lower (m : in_body SailModule.t)  : out_body SailModule.t Error.result =
  let+ main = method_of_main_process m.processes in
  { m with
    methods= main :: m.methods;
  } 
end
)