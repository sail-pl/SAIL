open Common
open TypesCommon
open Parser
open IrHir
open Error
open Result
open Monad.MonadSyntax(Error.MonadError)

let extract_type = function
| AstThir.Variable (_,t,_) | AstThir.Deref (_,t,_) | AstThir.StructRead (_,t,_,_)
| AstThir.ArrayRead (_,t,_,_) | AstThir.Literal (_,t,_) | AstThir.UnOp (_,t,_,_)
| AstThir.BinOp (_,t,_,_,_) | AstThir.Ref  (_,t,_,_) | AstThir.ArrayStatic (_,t,_)
| AstThir.StructAlloc (_,t,_,_) | AstThir.EnumAlloc  (_,t,_,_) | AstThir.MethodCall (_,t,_,_) -> t


let degenerifyType (t: sailtype) (generics: (string * sailtype ) list) loc : sailtype result =
  let rec aux = function
  | Bool -> ok Bool
  | Int -> ok Int 
  | Float -> ok Float
  | Char -> ok Char
  | String -> ok String
  | ArrayType (t,s) -> let+ t = aux t in ArrayType (t, s)
  | CompoundType (_name, _tl)-> error [ loc ,"todo compoundtype"]
  | Box t -> let+ t = aux t in Box t
  | RefType (t,m) -> let+ t = aux t in RefType (t,m)
  | GenericType t when generics = [] -> error [loc,Printf.sprintf "generic type %s present but empty generics list" t]
  | GenericType n -> 
    begin
      match List.assoc_opt n generics with
      | Some GenericType t -> GenericType t |> ok
      | Some t -> aux t
      | None -> error [loc,Printf.sprintf "generic type %s not present in the generics list" n]
    end
  in
  aux t

(*todo : generalize*)
let type_of_binOp (op:binOp) (operands_type:sailtype) : sailtype = match op with
  | Lt | Le | Gt | Ge | Eq | NEq | And | Or -> Bool
  | Plus | Mul | Div | Minus | Rem -> operands_type

module Pass : Pass.Body with
              type in_body = AstParser.expression AstHir.statement and   
              type out_body = AstThir.expression AstHir.statement = 
struct
  type in_body = AstParser.expression AstHir.statement
  type out_body = AstThir.expression AstHir.statement

   
  let matchArgParam (arg: sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: (string * sailtype ) list) loc : (sailtype * (string * sailtype ) list) result =
    let rec aux (a:sailtype) (m:sailtype) (g: (string * sailtype) list) = 
    match (a,m) with
    | Bool,Bool -> ok (Bool,g)
    | Int,Int -> ok (Int,g)
    | Float,Float -> ok (Float,g)
    | Char,Char -> ok (Char,g)
    | String,String -> ok (String,g)
    | ArrayType (at,s),ArrayType (mt,s') -> 
      if s = s' then
        let+ t,g = aux at mt g in ArrayType (t,s),g
      else
        error [loc,Printf.sprintf "array length mismatch : wants %i but %i provided" s' s]
    | CompoundType _, CompoundType _ -> error [loc, "todocompoundtype"]
    | Box _at, Box _mt -> error [loc,"todobox"]
    | RefType (at,am), RefType (mt,mm) -> if am <> mm then error [loc, "different mutability"] else aux at mt g
    | at,GenericType gt ->
     begin
        if List.mem gt generics then
          match List.assoc_opt gt g with
          | None -> ok (at,(gt,at)::g)
          | Some t -> if t = at then ok (at,g) else error [loc,"generic type mismatch"]
        else
          error [loc,Printf.sprintf "generic type %s not declared" gt]
      end
    | _ -> error [loc,Printf.sprintf "wants %s but %s provided" 
           (string_of_sailtype (Some m_param))
           (string_of_sailtype (Some arg))]
    in aux arg m_param resolved_generics  


  let check_call (name:string) (args: AstThir.expression list) (env:Pass.TypeEnv.t) loc : sailtype option result =
    match Pass.TypeEnv.get_function env (Method name)  with
    | Some (Method f) -> 
      begin
        let nb_args = List.length args and nb_params = List.length f.args in

          let* _ = if nb_args <> nb_params then error [loc, Printf.sprintf "unexpected number of arguments passed to %s : expected %i but got %i" name nb_params nb_args] else ok () in
          let* resolved_generics = List.fold_left2 
          (
            fun g ca (_,a) ->
              let* g in 
              let+ x = matchArgParam (extract_type ca) a f.generics g loc in
              snd x
          )  
          (ok [])
          args 
          f.args 
        in
        (* List.iter (fun (s,r) -> Printf.fprintf stdout "generic %s resolved to %s\n" s (string_of_sailtype (Some r)) ) resolved_generics; *)
        begin
          match f.ret with
          | Some r ->  let+ r = degenerifyType r resolved_generics loc in Some r
          | None -> ok None
        end
      end

    | None -> error [loc,"unknown method " ^ name]
    | _ -> error [loc,"problem with env"]

  let translate_expression (e : AstParser.expression) (te: Pass.TypeEnv.t) (generics : string list): AstThir.expression result = 
  let rec aux = function
    | AstParser.Variable (l,id) -> let+ t = Pass.TypeEnv.get_var te id l in AstThir.Variable(l,t,id)
    | AstParser.Deref (l,e) -> let* e = aux e in
      begin
        match e with
        | AstThir.Ref _ as t -> AstThir.Deref(l,extract_type t, e) |> ok
        | _ -> error [l,"can't deref a non-reference!"]
      end

    | AstParser.ArrayRead (l,array_exp,idx) -> let* array_exp = aux array_exp and* idx = aux idx in
      begin 
        match extract_type array_exp with
        | ArrayType (t,_) -> 
          let* _ = matchArgParam (extract_type idx) Int generics [] l in
          AstThir.ArrayRead(l,t,array_exp,idx) |> ok
        | _ -> error [l,"not an array !"]
      end

    | AstParser.StructRead (l,_struct_exp,_field) -> error [l,"todo: struct read"]
    | AstParser.Literal (l,li) -> let t = sailtype_of_literal li in AstThir.Literal(l,t,li) |> ok
    | AstParser.UnOp (l,op,e) -> let+ e = aux e in AstThir.UnOp (l, extract_type e,op,e)
    | AstParser.BinOp (l,op,le,re) ->  
      let* le = aux le and* re = aux re in
      let lt = extract_type le and rt = extract_type re in
      let+ t = matchArgParam lt rt generics [] l  in
      let op_t = type_of_binOp op (fst t) in
      AstThir.BinOp (l,op_t,op,le,re)

    | AstParser.Ref  (l,mut,e) -> let+ e = aux e in AstThir.Ref(l,RefType(extract_type e,mut),mut, e)
    | AstParser.ArrayStatic (l,el) -> 
      let* first_t = List.hd el |> aux  in
      let first_t = extract_type first_t in
      let el,errors = partition_result (
        fun e -> let* t = aux e in
        if extract_type t = first_t then ok t else error [l,"mixed type array"]
      ) el in 
      if errors = [] then
        let t = ArrayType (first_t, List.length el) in AstThir.ArrayStatic(l,t,el)  |> ok
      else
        Error errors

    | AstParser.StructAlloc (l,_name,_fields) -> error [l, "todo: struct alloc"]
    | AstParser.EnumAlloc (l,_name,_el) -> error [l, "todo: enum alloc"]
    | AstParser.MethodCall (l,name,args) -> 
      let args,errors = partition_result aux args in 

      if errors = [] then
        let* res = check_call name args te l in
        match res with
        | None -> error [l,"trying to use the result of void method"]
        | Some t -> AstThir.MethodCall(l, t, name, args) |> ok
      else
        Error errors


    in aux e


  let lower c env generics = 
    let rec aux s (te:Pass.TypeEnv.t) = match s with
      | AstHir.DeclVar (l, mut, id, t, (optexp : AstParser.expression option)) -> 
        let optexp = Option.MonadOption.(>>|) optexp  (fun e -> translate_expression e te generics) in 
        begin
          let* var_type =             
            match (t,optexp) with
            | (Some t,Some e) -> let* e in let tv = extract_type e in let+ a = matchArgParam tv t generics [] l in fst a
            | (Some t, None) -> ok t
            | (None,Some t) -> let+ t in extract_type t
            | (None,None) -> error [l,"can't infere type with no expression"]
            
          in 
          let* te' = Pass.TypeEnv.declare_var te id var_type l in 
          
          match optexp with
          | None -> ok (AstHir.DeclVar (l,mut,id,t,None),te')
          | Some e -> let+ e in AstHir.DeclVar (l,mut,id,t,Some e),te'
        end
        
      | AstHir.DeclSignal(loc, s) -> ok (AstHir.DeclSignal(loc, s),te)
      | AstHir.Skip (loc) -> ok (AstHir.Skip(loc),te)
      | AstHir.Assign(loc, e1, e2) -> 
        let* e1 = translate_expression e1 te generics
        and* e2 = translate_expression e2 te generics in
        let* _ = matchArgParam (extract_type e1) (extract_type e2) [] [] loc in
        ok (AstHir.Assign(loc, e1, e2),te)

      | AstHir.Seq(loc, c1, c2) -> 
        let* c1,te1 = aux c1 te in
        let+ c2,te2 = aux c2 te1 in
        AstHir.Seq(loc, c1, c2) ,te2

      | AstHir.Par(loc, c1, c2) -> 
        let* c1,te1 = aux c1 te in
        let+ c2,te2 = aux c2 te1 in
        AstHir.Par(loc, c1, c2),te2

      | AstHir.If(loc, cond_exp, then_s, else_s) -> 
        let* cond_exp = translate_expression cond_exp te generics in
        let* _ = matchArgParam (extract_type cond_exp) Bool [] [] loc in
        let* res,_ = aux then_s te in
        begin
        match else_s with
        | None -> ok (AstHir.If(loc, cond_exp, res, None),te)
        | Some s -> let+ s,_ = aux s te in (AstHir.If(loc, cond_exp, res, Some s),te)
        end

      | AstHir.While(loc,e,c) -> 
        let* e = translate_expression e te generics in
        let+ t,_ = aux c te in
        AstHir.While(loc,e,t),te

      | AstHir.Case(loc, e, _cases) ->
        let+ e = translate_expression e te generics in
        AstHir.Case (loc, e, []),te


      | AstHir.Invoke(loc, ign, id, el) -> 
        let el,errors = partition_result (fun e -> translate_expression e te generics) el in
        
        if errors = [] then
          let+ _ = check_call id el env loc in
          AstHir.Invoke(loc, ign, id,el),te
        else error errors

      | AstHir.Return(_, None) as r -> ok (r,te)

      | AstHir.Return(loc, Some e) ->
        let+ e = translate_expression e te generics in
        AstHir.Return(loc, Some e),te

      | AstHir.Run(loc, id, el) ->
        let el,errors = partition_result (fun e -> translate_expression e te generics) el in
        if errors = [] then
          let+ _ = check_call id el env loc in
          AstHir.Run(loc, id, el),te
        else error errors

      | AstHir.Emit(loc, s) -> ok (AstHir.Emit(loc,s),te)
      | AstHir.Await(loc, s) -> ok (AstHir.When(loc, s, AstHir.Skip(loc)),te)
      | AstHir.When(loc, s, c) -> let+ res,_ = aux c te in AstHir.When(loc, s, res),te

      | AstHir.Watching(loc, s, c) -> let+ res,_ = aux c te in AstHir.Watching(loc, s, res),te
      | AstHir.Block (loc, c) -> 
        let+ res,te' = aux c (Pass.TypeEnv.new_frame te) in 
        AstHir.Block(loc,res),te'
    in 
    let+ res,_ = aux c env in res
end