open Llvm
open Common
open TypesCommon
open CodegenEnv
open Monad.UseMonad(Logging.Logger)

type llvm_args = { c:llcontext; b:llbuilder;m:llmodule; layout : Llvm_target.DataLayout.t}
let mangle_method_name (name:string) (mname:string) (args: sailtype list ) : string =
  let back = List.fold_left (fun s t -> s ^ string_of_sailtype (Some t) ^ "_"  ) "" args in
  let front = "_" ^ mname ^ "_" ^ name ^ "_" in
  let res = front ^ back in
  (* Logs.debug (fun m -> m "renamed %s to %s" name res); *)
  res

let getLLVMLiteral (l:literal) (llvm:llvm_args) : llvalue =
  match l with
  | LBool b -> const_int (i1_type llvm.c) (Bool.to_int b)
  | LInt i -> const_int_of_string (integer_type llvm.c i.size) (Z.to_string i.l) 10
  | LFloat f -> const_float (double_type llvm.c) f
  | LChar c -> const_int (i8_type llvm.c) (Char.code c)
  | LString s -> build_global_stringptr  s ".str" llvm.b

let ty_of_alias(t:sailtype) env : sailtype  =
  match snd t with
  | CompoundType  {origin=Some (_,mname); name=(_,name);decl_ty=Some T ();_} -> 
    begin
    match DeclEnv.find_decl name (Specific (mname,Type)) env with 
    | Some {ty=Some t';_} -> t'
    | Some {ty=None;_} -> t
    | None -> failwith @@ Fmt.str "ty_of_alias :  '%s' not found in %s" (string_of_sailtype (Some t)) mname
    end
  | _ ->  t

let unary (op:unOp) (t,v) : llbuilder -> llvalue = 
  let f = 
    match snd t,op with
    | Float,Neg -> build_fneg
    | Int _,Neg -> build_neg
    | _,Not  -> build_not
    | _ -> Printf.sprintf "bad unary operand type : '%s'. Only double and int are supported" (string_of_sailtype (Some t)) |> failwith
  in f v ""
  
  
let binary (op:binOp) (t:sailtype) (l1:llvalue) (l2:llvalue) : llbuilder -> llvalue = 
  let operators = function
    | Int _ -> 
      Some [
        (Minus, build_sub) ; (Plus, build_add) ; (Rem, build_srem) ;
        (Mul,build_mul) ; (Div, build_sdiv) ; 
        (Eq, build_icmp Icmp.Eq) ; (NEq, build_icmp Icmp.Ne) ;
        (Lt, build_icmp Icmp.Slt) ; (Gt, build_icmp Icmp.Sgt) ; 
        (Le, build_icmp Icmp.Sle) ; (Ge, build_icmp Icmp.Sge) ;
        (And, build_and) ; (Or, build_or) ;
      ]
    | Char ->
    Some [
      (Minus, build_sub) ; (Plus, build_add) ; (Rem, build_srem) ;
      (Mul,build_mul) ; (Div, build_sdiv) ; 
      (Eq, build_icmp Icmp.Eq) ; (NEq, build_icmp Icmp.Ne) ;
      (Lt, build_icmp Icmp.Slt) ; (Gt, build_icmp Icmp.Sgt) ; 
      (Le, build_icmp Icmp.Sle) ; (Ge, build_icmp Icmp.Sge) ;
      (And, build_and) ; (Or, build_or) ;
    ]
  
    | Float ->
      Some [
        (Minus, build_fsub) ; (Plus, build_fadd) ; (Rem, build_frem) ;
        (Mul,build_fmul) ; (Div, build_fdiv) ; 
        (Eq, build_fcmp Fcmp.Oeq) ; (NEq, build_fcmp Fcmp.One) ;
        (Lt, build_fcmp Fcmp.Olt) ; (Gt, build_fcmp Fcmp.Ogt) ; 
        (Le, build_fcmp Fcmp.Ole) ; (Ge, build_fcmp Fcmp.Oge) ;
      ]
    | _ -> None
  in
  let string_of_binop = function Minus -> "minus" | Plus -> "plus" | Rem -> "rem" | Eq -> "equal" 
  | And -> "and" | Or -> "or" | Le -> "le" | Lt -> "lt" | Ge -> "ge" | Gt -> "gt" | Mul -> "mul"
  | NEq -> "neq" | Div -> "div"
  in
  let t = if snd t = Bool then fst t,Int 1 else t in (* thir will have checked for correctness *)
  let l = operators (snd t) in
  let open Common.Monad.MonadOperator(Common.MonadOption.M) in
  match l >>| List.assoc_opt op |> Option.join with
  | Some oper -> oper l1 l2 ""
  | None -> Printf.sprintf "codegen: bad usage of binop '%s' with type %s" (string_of_binop op) (string_of_sailtype @@ Some t) |> failwith


let toLLVMArgs (args: param list ) (env:DeclEnv.t) (llvm:llvm_args) : (bool * sailtype * llvalue) array E.t = 
  ListM.map (
    fun {id;mut;ty=t;_} -> 
      let+ ty = getLLVMType env t llvm.c llvm.m in 
      mut,t,build_alloca ty id llvm.b
  ) args <&> Array.of_list 


let get_memcpy_intrinsic llvm = 
  let args_type = [|i8_type llvm.c |> pointer_type; i8_type llvm.c |> pointer_type ; i64_type llvm.c; i1_type llvm.c|] in

  let f = declare_function "llvm.memcpy.p0i8.p0i8.i64" (function_type (void_type llvm.c) args_type ) llvm.m in
  f