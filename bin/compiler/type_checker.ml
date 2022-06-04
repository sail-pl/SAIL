open Common
open Compiler_common
open Ast


let sailtype_of_literal = function
  | LBool _ -> Bool
  | LFloat _ -> Float
  | LInt _ -> Int
  | LChar _ -> Char
  | LString _ -> String

let print_method_proto (name:string) (methd: sailor_method) =
    let _,args_type = List.split methd.decl.args in
    let args = String.concat "," (List.map (fun t -> string_of_sailtype (Some t)) args_type) in
    let methd_string = Printf.sprintf "method %s : %s" name args in
    Logs.debug (fun m -> m "%s" methd_string)

let print_process_proto (name:string) (proc: sailor_process) =
  let _,args_type = List.split proc.args in
  let args = String.concat "," (List.map (fun t -> string_of_sailtype (Some t)) args_type) in
  let methd_string = Printf.sprintf "process %s : %s" name args in
  Logs.debug (fun m -> m "%s" methd_string)

let print_callsMap {methodMap; processMap; _} =
  FieldMap.iter print_method_proto methodMap;
  FieldMap.iter print_process_proto processMap


(* todo : use sail_env *)
let current_frame = function [] -> failwith "phase1 environnement is empty !" | (h::t) ->  h,t

let push_frame ts s = s :: ts

let pop_frame = function _::t  -> t | [] -> Logs.warn (fun m -> m "popping empty frame"); []

let new_frame ts =
  let c = FieldMap.empty in
  push_frame ts c

let get_var e name = 
  let rec aux env = 
    let current,next = current_frame env in
    match FieldMap.find_opt name current with 
    | Some v -> v
    | None  when env = [] ->  Printf.sprintf "variable %s doesn't exists !" name |> failwith
    | _ -> aux next
    in aux e

let declare_var ts name value =
  let current,next = current_frame ts in
  match FieldMap.find_opt name current with 
  | Some _ -> Printf.sprintf "variable %s already exists !" name |> failwith
  | None -> 
    let upd_frame = FieldMap.add name value current in
    push_frame next upd_frame

(* end todo *)


(* do some basic type checking and monomorphize *)
let analyse_statement (s: Ast.statement) (args: sailtype FieldMap.t) (sm : Ast.statement sailModule) (ext: sailor_externals) (sc:sailor_callables) : sailor_callables =
  
  let resolveType (arg: sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: sailor_args) : sailtype * sailor_args =
    let rec aux (a:sailtype) (m:sailtype) (g:sailor_args) = match (a,m) with
    | Bool,Bool -> Bool,g
    | Int,Int -> Int,g
    | Float,Float -> Float,g
    | Char,Char -> Char,g
    | String,String -> String,g
    | ArrayType at,ArrayType mt -> let t,g = aux at mt g in ArrayType t,g
    | CompoundType _, CompoundType _ -> failwith "todo"
    | Box _at, Box _mt -> failwith "todo"
    | RefType (_at,_am), RefType (_mt,_mm) -> failwith "todo"
    | GenericType _,_ -> failwith "can't have generic argument"
    | at,GenericType gt -> 
      begin
      if List.mem gt generics then
        match List.assoc_opt gt g with
        | None -> at,(gt,at)::g
        | Some t -> if t = at then at,g else failwith "generic argument mismatch"
      else
        failwith "generic argument not declared"
      end
    | _ -> Printf.sprintf "wants %s but %s provided" 
           (string_of_sailtype (Some m))
           (string_of_sailtype (Some a))
          |> failwith 
    in
    match arg with
    | GenericType _ -> failwith "can't have generic argument"
    | _ -> aux arg m_param resolved_generics
    
  in

  let check_args (caller_args:sailtype list) (args:sailtype list) (generics : string list) : sailor_args = 
    if List.length caller_args <> List.length args then
      failwith "wrong number of arguments";
      Logs.debug (fun m-> m "caller args : ");
      List.iter (fun t -> Logs.debug (fun m-> m "%s " (string_of_sailtype (Some t)))) caller_args;
      Logs.debug (fun m-> m "method args : ");
      List.iter (fun t -> Logs.debug (fun m-> m "%s " (string_of_sailtype (Some t)))) args;

    List.fold_left2 (
      fun g ca a -> 
        resolveType ca a generics g |> snd
    ) ([]) caller_args args
  in

  let rec construct_call (calle:string) (el:expression list) (ts : varTypesMap) (sc:sailor_callables) : sailtype option * sailor_callables = 
    Logs.debug (fun m -> m "found call to %s" calle);
    
    (* we construct the types of the args (and collect extra new calls) *)
    let call_args,sc' = List.fold_left (
      fun (l,sc) e -> let t,sc' = analyse_expression e ts sc in (t::l,sc')
    ) ([],sc) el in

    let call_args = List.rev call_args in
    (* we check if the calle is external *)
    match List.assoc_opt calle ext with
    | None -> 
      begin
        (* we check if we are calling a method *)
        let r_type,args,generics,body = match List.find_opt (fun m -> m.m_name = calle) sm.methods with
        | None -> 
          (* if not we check if it's a process *)
            begin
              match List.find_opt (fun p -> p.p_name = calle) sm.processes with
              | None ->  calle ^ " is not declared" |> failwith
              | Some p -> 
                let g = p.p_interface |> fst in
                None,g,p.p_generics,p.p_body
            end
        | Some m -> m.m_rtype,m.m_params,m.m_generics,m.m_body
        in

        (* we make sure they correspond to what the callable wants *)
        (* if the callable is generic we check all the generic types are present at least once *)
        (* 
          we build a (string*sailtype) list of generic to type correspondance
          if the generic is not found in the list, we add it with the corresponding type
          if the generic already exists with the same type as the new one, we are good else we fail 
        *)

        let args_name,args_type = List.split args in
        let resolved_generics = check_args call_args args_type generics in
        let ret = match r_type with
        | Some t -> Some (degenerifyType t resolved_generics)
        | None -> None
        in
        let name = mangle_method_name calle call_args in
        let call : sailor_method = {body; decl={ret; args=(List.combine args_name call_args)}; generics=resolved_generics} in 
        let methodMap = FieldMap.add name call sc'.methodMap in 
        ret,{sc' with methodMap}
      end
    | Some (decl,generics,_) -> 
      let arg_types = List.split decl.args |> snd in
      check_args call_args arg_types generics  |> ignore;
      decl.ret,sc'

  and analyse_expression (e:expression) (ts : varTypesMap) (sc : sailor_callables) : sailtype * sailor_callables =
  let rec aux e sc = match e with
  | Variable s -> get_var ts s, sc
  | MethodCall (name,el) -> 
    begin
      match construct_call name el ts sc with
      | None,_ -> "trying to use the result of void function " ^ name |> failwith
      | Some t,sc -> t,sc
    end
  | Literal l -> sailtype_of_literal l, sc
  | StructRead (_,_) -> failwith "todo"
  | ArrayRead (e,_) -> 
    begin 
      match aux e sc with
      | (ArrayType t,sc) -> t,sc
      | _ -> failwith "not an array !"
    end
  | UnOp (_,e) -> aux e sc
  | BinOp (_,e1,e2) -> 
    let t1,sc' = aux e1 sc in let t2,sc' = aux e2 sc' in
    if t1 <> t2 then failwith "operands do not have the same type !" else t1,sc'

  | Ref (m,e) -> let t,sc' = aux e sc in RefType (t,m),sc'
  | Deref e -> let t,sc' = aux e sc in
    begin
      match t with
      | RefType _ -> t,sc'
      | _ -> failwith "can't deref a non-reference!"
    end
  | ArrayStatic (e::h) -> 
    let first_t,sc' = aux e sc in
    let t,v = List.fold_left (
      fun (last_t,sc') e -> 
        let next_t,next_ts = aux e sc' in
        if next_t <> last_t then failwith "mixed type array !" else (next_t,next_ts)
    ) (first_t,sc') h in
    ArrayType t,v
  | ArrayStatic [] -> failwith "error : empty array"
  | StructAlloc (_,_) -> failwith "todo"
  | EnumAlloc (_,_) -> failwith "todo"
  in aux e sc
  
    (*todo : more checks (arrays...) *)
  and analyse_statement (st:statement) (ts : varTypesMap) (sc : sailor_callables) : varTypesMap * sailor_callables = match st with
  | Invoke (_,name,el) -> let rt,sc' = construct_call name el ts sc in 
    if Option.is_some rt then
      Logs.warn (fun m -> m "result of non-void function %s is discarded" name);
    ts,sc'

  | DeclVar (_,name,t,None) -> declare_var ts name t,sc
  | DeclVar (_,name,t,Some e) -> 
    let t_r,sc' = analyse_expression e ts sc in 
    if t <> t_r then failwith "type declared and assigned mismatch !"
    else declare_var ts name t,sc'

  | Block s -> let new_ts,sc' = analyse_statement s (new_frame ts) sc in pop_frame new_ts,sc'
  | Seq (s1,s2) -> let ts',sc' = analyse_statement s1 ts sc in analyse_statement s2 ts' sc'
  | Assign (el,er) -> 
    let t_l,sc_l = analyse_expression el ts sc in
    let t_r,sc_r = analyse_expression er ts sc_l in 
    if t_l <> t_r then failwith "type declared and assigned mismatch !" else ts,sc_r

  | If (e,s1, Some s2) -> let sc' = analyse_expression e ts sc |> snd in
    let sc' = analyse_statement s1 ts sc' |> snd in analyse_statement s2 ts sc'

  | If (e,s, None) -> let sc' = analyse_expression e ts sc |> snd in analyse_statement s ts sc'
  | While (e,s) -> let sc' = analyse_expression e ts sc |> snd in analyse_statement s ts sc'
  (* todo : check return type *)
  | Return Some e -> let sc' = analyse_expression e ts sc |> snd in ts,sc'
  | Return None -> ts,sc
  | Loop s -> analyse_statement s ts sc
  | _ -> ts,sc (* todo : other stuffs *)
  
  in 
  analyse_statement s [args] sc |> snd


let method_start_env (m:Ast.statement method_defn) : sailtype FieldMap.t = 
  let f = fun m (n,t) -> FieldMap.add n t m in
  List.fold_left f FieldMap.empty m.m_params 

let process_start_env (p:Ast.statement process_defn) : sailtype FieldMap.t = 
  let f = fun m (n,t) -> FieldMap.add n t m in
  List.fold_left f FieldMap.empty (fst p.p_interface)


let analyse_method (m: Ast.statement method_defn) (sm : Ast.statement sailModule) (ext:sailor_externals) (sc:sailor_callables) : sailor_callables = 
  let methodMap = 
    if m.m_generics = [] then
    (* method isn't generic, we add it *)
      let name = mangle_method_name m.m_name (List.split m.m_params |> snd) in 
      let methd = {body=m.m_body; decl={ret=m.m_rtype; args=m.m_params}; generics=[]} in
      FieldMap.add name methd sc.methodMap
  else
    sc.methodMap
  in
  analyse_statement m.m_body (method_start_env m) sm ext {sc with methodMap}

let analyse_process (p:Ast.statement process_defn) (sm : Ast.statement sailModule) (ext:sailor_externals) (sc:sailor_callables) : sailor_callables =
  let processMap = 
    if p.p_generics = [] then
      let args = p.p_interface |> fst in 
    (* process isn't generic, we add it *)
      let name = mangle_method_name p.p_name (List.split args |> snd) in
      let proc = {body=p.p_body; args; generics=[]} in
      FieldMap.add name proc sc.processMap
    else
      sc.processMap
    in
    analyse_statement p.p_body (process_start_env p) sm ext {sc with processMap}

let type_check_module (a: Ast.statement Common.sailModule) : sailor_callables = 
  Logs.debug (fun m -> m "analysing types");
  let externals = Externals.get_externals () in
  let callables : sailor_callables = { methodMap=FieldMap.empty; processMap=FieldMap.empty }
  |> fun c -> List.fold_left (fun sc m -> analyse_method m a externals sc) c a.methods
  |> fun c -> List.fold_left (fun sc p -> analyse_process p a externals sc) c a.processes in
  Logs.debug (fun m -> m "deduced declarations :");
  print_callsMap callables;
  callables