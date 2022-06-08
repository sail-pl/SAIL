open Common
open Compiler_common
open Ast_hir


let externals = Externals.get_externals ()


type monomorphics = sailor_args string_assoc

let sailtype_of_literal = function
  | LBool _ -> Bool
  | LFloat _ -> Float
  | LInt _ -> Int
  | LChar _ -> Char
  | LString _ -> String

let print_method_proto (name:string) (methd: sailor_method) =
    let _,args_type = List.split methd.decl.args in
    let args = String.concat "," (List.map (fun t -> string_of_sailtype (Some t)) args_type) in
    let methd_string = Printf.sprintf "method %s (%s)" name args in
    Logs.debug (fun m -> m "%s" methd_string)


(* todo : use sail_env *)
let current_frame = function [] -> failwith "environnement is empty !" | (h::t) ->  h,t

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
    | None when next = [] ->  Printf.sprintf "variable %s doesn't exist !" name |> failwith
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


let find_callable (name:string) (sm : statement sailModule) : sailor_function = 
  (* we check if the calle is external *)
  let args,generics,body,ty,r_type = match List.assoc_opt name externals with
  | None -> 
    begin
    (* we check if we are calling a method *)
      match List.find_opt (fun m -> m.m_name = name) sm.methods with
    | Some m -> m.m_params, m.m_generics, Some m.m_body, FMethod, m.m_rtype

      | None -> 
        (* if not we check if it's a process *)
        begin
          match List.find_opt (fun p -> p.p_name = name) sm.processes with
          | None ->  name ^ " is not declared" |> failwith
          | Some p -> fst p.p_interface, p.p_generics, Some p.p_body, FProcess, None
          end
      end
  | Some {decl;generics;_} -> decl.args, generics ,None, FExternal, decl.ret
  in
  {name;generics;body;ty;r_type;args}


(* do some basic type checking and monomorphize *)
let type_check (f: sailor_function) (env: sailtype FieldMap.t) (sm : statement sailModule) (monos:monomorphics) (funs:sailor_functions) : monomorphics * sailor_functions =
  
  let resolveType (arg: sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: sailor_args) : sailtype * sailor_args =
    let rec aux (a:sailtype) (m:sailtype) (g:sailor_args) = 
      match (a,m) with
    | Bool,Bool -> Bool,g
    | Int,Int -> Int,g
    | Float,Float -> Float,g
    | Char,Char -> Char,g
    | String,String -> String,g
    | ArrayType (at,s),ArrayType (mt,s') -> 
      if s = s' then
        let t,g = aux at mt g in ArrayType (t,s),g
      else
        Printf.sprintf "array length mismatch : wants %i but %i provided" s' s  |> failwith
    | CompoundType _, CompoundType _ -> failwith "todocompoundtype"
    | Box _at, Box _mt -> failwith "todobox"
    | RefType (at,am), RefType (mt,mm) -> if am <> mm then failwith "different mutability" else aux at mt g
    | GenericType _,GenericType _ -> GenericType "Y",g
    | at,GenericType gt -> 
      begin
      if List.mem gt generics then
        match List.assoc_opt gt g with
        | None -> at,(gt,at)::g
        | Some t -> if t = at then at,g else failwith "generic type mismatch"
      else
        Printf.sprintf "generic type %s not declared" gt |> failwith
      end
    | _ -> Printf.sprintf "wants %s but %s provided" 
           (string_of_sailtype (Some m))
           (string_of_sailtype (Some a))
          |> failwith 
    in
    aux arg m_param resolved_generics
    
  in

  let check_args (caller_args:sailtype list) (args:sailtype list) (generics : string list) : sailor_args = 
    if List.length caller_args <> List.length args then
      failwith "wrong number of arguments";
      Logs.debug (fun m-> m "caller args : %s" (List.fold_left (fun acc t -> Printf.sprintf "%s %s," acc (string_of_sailtype (Some t))  ) "" caller_args));
      Logs.debug (fun m-> m "method args : %s" (List.fold_left (fun acc t -> Printf.sprintf "%s %s," acc (string_of_sailtype (Some t))  ) "" args));

    List.fold_left2 (
      fun g ca a -> 
        resolveType ca a generics g |> snd
    ) ([]) caller_args args
  in

  let rec construct_call (calle:string) (el:Ast_parser.expression list) (ts : varTypesMap) (monos:monomorphics) (funs:sailor_functions) : sailtype option * monomorphics * sailor_functions = 
    Logs.debug (fun m -> m "found call to %s" calle);
    (* only methods can be recursive *)
    if calle = f.name && f.ty = FProcess then failwith "processes can't be recursive!";


    (* we construct the types of the args (and collect extra new calls) *)
    let call_args,monos',sc' = List.fold_right (
      fun e (l,monos,sc)-> 
        let t,monos',sc' = analyse_expression e ts monos sc in (t::l,monos',sc')
    )  el ([],monos,funs) in


    let f = find_callable calle sm in

    
    match f.body with
    | Some b -> (* process and method *)
      let args_name,args_type = List.split f.args in


        (* we make sure they correspond to what the callable wants *)
        (* if the callable is generic we check all the generic types are present at least once *)
        (* 
          we build a (string*sailtype) list of generic to type correspondance
          if the generic is not found in the list, we add it with the corresponding type
          if the generic already exists with the same type as the new one, we are good else we fail 
        *)

        let resolved_generics = check_args call_args args_type (f.generics) in
        List.iter (fun (n,t) -> Logs.debug (fun m -> m "resolved %s to %s " n (string_of_sailtype (Some t)))) resolved_generics;

        begin
          if List.compare_lengths resolved_generics f.generics != 0 then 
              failwith "problem";

          List.iter (fun (s,r) -> Logs.debug (fun m -> m "generic %s resolved to %s" s (string_of_sailtype (Some r)) )) resolved_generics;

          let monos' = (calle,resolved_generics)::monos' in

          let ret = match f.r_type with
          | Some t -> Some (degenerifyType t resolved_generics)
          | None -> None
          in
          let name = mangle_method_name calle call_args in
          let call : sailor_method = {body=b; decl={ret; args=(List.combine args_name call_args)}; generics=resolved_generics} in 
          let funs' = FieldMap.add name call funs in 
          ret,monos',funs'
        end
    | None -> (* external method *)
      begin
        let arg_types = List.split f.args |> snd in
        check_args call_args arg_types f.generics  |> ignore;
        f.r_type,monos',sc'
      end
  

  and analyse_command (_cmd: statement) (_ts : varTypesMap) (_monos : monomorphics) (_funs : sailor_functions) : varTypesMap * monomorphics * sailor_functions =
      match f.ty with
      | FProcess -> failwith "todo: typecheck commands"
      | _ -> failwith "Methods can't have reactive statements!"


  and analyse_expression (e:Ast_parser.expression) (ts : varTypesMap) (monos : monomorphics) (funs : sailor_functions) : sailtype * monomorphics * sailor_functions =
    let rec aux e monos sc = match e with
    | Ast_parser.Variable (_, s) -> get_var ts s, monos, sc
    | MethodCall (_, name,el) -> 
      begin
        match construct_call name el ts monos sc with
        | None,_,_ -> "trying to use the result of void function " ^ name |> failwith
        | Some t,monos',sc -> t, monos', sc
      end
    | Literal (_, l) -> sailtype_of_literal l, monos, sc
    | StructRead (_, _,_) -> failwith "todo: struct read"
    | ArrayRead (_, e,idx) -> 
      begin 
        match aux e monos sc with
        | ArrayType (t,_),monos',sc' -> 
          let idx_t,monos',sc' = aux idx monos' sc' in
          begin
            try
              resolveType idx_t Int [] [] |> ignore;           
              t,monos',sc'
            with Failure s -> Printf.sprintf "incorrect index type : %s " s |> failwith 
          end
        | _ -> failwith "not an array !"
      end
    | UnOp (_,_,e) -> aux e monos sc 
    | BinOp (_,_,e1,e2) -> 
      let t1,monos',sc' = aux e1 monos sc in let t2,monos',sc' = aux e2 monos' sc' in
      begin
        try
          resolveType t1 t2 [] [] |> ignore;           
          t1,monos',sc'
        with Failure s -> Printf.sprintf "operands mismatch : %s " s |> failwith 
      end 

    | Ref (_,m,e) -> let t,monos',sc' = aux e monos sc in RefType (t,m),monos',sc'
    | Deref (_, e) -> let t,monos',sc' = aux e monos sc in
      begin
        match t with
        | RefType _ -> t,monos',sc'
        | _ -> failwith "can't deref a non-reference!"
      end
    | ArrayStatic (_, e::h) -> 
      let first_t,monos',sc' = aux e monos sc in
      let t,monos',v = List.fold_left (
        fun (last_t,monos',sc') e -> 
          let next_t,monos',next_ts = aux e monos' sc' in
          try
            resolveType next_t last_t [] [] |> ignore;
            next_t,monos',next_ts
          with Failure s -> Printf.sprintf "mixed type array : %s " s |> failwith 
      ) (first_t,monos',sc') h in
      ArrayType (t, List.length (e::h)),monos',v

    | ArrayStatic (_, []) -> failwith "error : empty array"
    | StructAlloc (_, _,_) -> failwith "todo: struct alloc"
    | EnumAlloc (_, _,_) -> failwith "todo: enum alloc"
    in aux e monos funs
  

    (*todo : more checks (arrays...) *)
  and analyse_statement (st:statement) (ts : varTypesMap) (monos:monomorphics) (funs : sailor_functions) : varTypesMap * monomorphics * sailor_functions = match st with
  | DeclVar (_, _,name,t,None) -> declare_var ts name t,monos,funs
  | DeclVar (_, _,name,t,Some e) -> 
    begin
      let t_r,monos',sc' = analyse_expression e ts monos funs in 
      try
        resolveType t t_r [] [] |> ignore;
        declare_var ts name t,monos',sc'
      with Failure s -> Printf.sprintf "type declared and assigned mismatch : %s " s |> failwith 
    end
  | Block (_, s) -> let new_ts,monos',sc' = analyse_statement s (new_frame ts) monos funs in pop_frame new_ts,monos',sc'
  | Seq (_, s1,s2) -> let ts',monos',sc' = analyse_statement s1 ts monos funs in analyse_statement s2 ts' monos' sc'
  | Assign (_, el,er) -> 
    let t_l,monos_l,sc_l = analyse_expression el ts monos funs in
    let t_r,monos_r,sc_r = analyse_expression er ts monos_l sc_l in 
    begin
      try
        resolveType t_l t_r [] [] |> ignore;
        ts,monos_r,sc_r
      with Failure s -> Printf.sprintf "type declared and assigned mismatch : %s " s |> failwith 
    end
  | If (_, e,s1, Some s2) -> let _,monos',sc' = analyse_expression e ts monos funs in
    let _,monos',sc' = analyse_statement s1 ts monos' sc' in analyse_statement s2 ts monos' sc'

  | If (_, e,s, None) -> let _,monos',sc' = analyse_expression e ts monos funs in analyse_statement s ts monos' sc'
  | While (_, e,s) -> let _,monos',sc' = analyse_expression e ts monos funs in analyse_statement s ts monos' sc'

  | Return (_,Some _ ) when f.ty = FProcess -> failwith "can't have non-void return inside a process"
  | Return (_, Some e) -> 
    if Option.is_some f.r_type then
      let t,monos',sc' = analyse_expression e ts monos funs in 
      try
      resolveType (Option.get f.r_type) t [] [] |> ignore; ts,monos',sc' 
      with Failure s -> "incorrect return: " ^ s |> failwith
    else failwith "missing return type"
  | Return (_, None) ->  if Option.is_some f.r_type then failwith "non-void return type" else ts,monos,funs
  (*| Loop (_, s) -> analyse_statement s ts monos funs*)
  | Invoke (_, _,name,el) -> let rt,monos',sc' = construct_call name el ts monos funs in 
    if Option.is_some rt then
      Logs.warn (fun m -> m "result of non-void function %s is discarded" name);
    ts,monos',sc'
  | Skip _ -> ts,monos,funs
  | Case _ -> failwith "todo: pattern matching"
  | DeclSignal _ | Par _ | Run _ | Emit _ | Await _ | When _ | Watching _ -> analyse_command st ts monos funs
    
  
  in 
  match f.ty with
  | FExternal -> monos,funs (* nothing to do for externals functions *)
  | FProcess | FMethod -> 
    (* if not generic, safe to add it *)
    let funs = if f.generics = [] then 
      let name = mangle_method_name f.name (f.args |> List.split |> snd) in
      let call : sailor_method = {body= Option.get f.body; decl={ret=f.r_type; args=f.args}; generics=[]} in 
      FieldMap.add name call funs 
    else funs

    in 
    let _,monos',funs' = analyse_statement (Option.get f.body) [env] monos funs in (monos',funs')



let analyse_functions (monos:monomorphics) (sm : statement sailModule) : sailor_functions =
  if monos = [] then failwith "no monomorphic callable (no main?)";

  let check_fun (name,(g:sailor_args)) (monos:monomorphics) (funs:sailor_functions): monomorphics * sailor_functions = 
    let f = find_callable name sm in

    (* we apply eventual type substitutions *)
    let args = List.map (fun (n,t) -> n,(degenerifyType t g)) f.args in

    let r_type = match f.r_type with
    | Some t -> Some (degenerifyType t g)
    | None -> None
  in

    let f =  {f with args;r_type} in
    let start_env = List.fold_left (fun m (n,t) -> FieldMap.add n t m) FieldMap.empty f.args in
    type_check f start_env sm monos funs

  in
  (* the monomorphic part returned should eventually contain new monorphic variants found *)

  let rec aux (m:monomorphics) (funs:sailor_functions) : monomorphics * sailor_functions = 
    match m with
    | [] -> monos,funs
    | (name,resolved_gens)::t -> 
      let mname = mangle_method_name name (List.split resolved_gens |> snd) in
      let m',funs' = match FieldMap.find_opt mname funs with
      | Some _ -> 
        Logs.debug (fun m -> m "%s already checked" mname);
        t,funs
      | None -> 
        Logs.info (fun m -> m "typechecking %s" mname);
          check_fun (name,resolved_gens) t funs
      in
      aux m' funs'
      
  in
  let funs = aux monos FieldMap.empty |> snd in
  Logs.info (fun m -> m "generated %i function declarations" (List.length (FieldMap.bindings funs)));
  funs



let type_check_module (a: statement sailModule) : sailor_functions = 
  (* we only typecheck monomorphic declarations *)
  let monos = 
    let test funs name has_gen = if has_gen then funs else (name,[])::funs in
    []
    |> fun l -> List.fold_left (fun acc m -> test acc m.m_name (m.m_generics <> [])) l a.methods
    |> fun l -> List.fold_left (fun acc p -> test acc p.p_name (p.p_generics <> [])) l a.processes
    |> fun l -> List.fold_left (fun acc (name,e) -> test acc name (e.generics <> [])) l externals

  in let funs = analyse_functions monos a 
  in FieldMap.iter print_method_proto funs; funs