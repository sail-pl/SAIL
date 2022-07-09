open Common
open Pass
open TypesCommon
open IrHir
open Error
open Error.MonadError
open MonadOption
open Monad.MonadOperator(M)
open Monad.MonadSyntax(Error.MonadError)
open Result


type expression = (loc * sailtype) AstHir.expression

type statement = expression AstHir.statement

let extract_exp_loc_ty = function
| AstHir.Variable (lt,_) | AstHir.Deref (lt,_) | AstHir.StructRead (lt,_,_)
| AstHir.ArrayRead (lt,_,_) | AstHir.Literal (lt,_) | AstHir.UnOp (lt,_,_)
| AstHir.BinOp (lt,_,_,_) | AstHir.Ref  (lt,_,_) | AstHir.ArrayStatic (lt,_)
| AstHir.StructAlloc (lt,_,_) | AstHir.EnumAlloc  (lt,_,_) -> lt

let extract_statements_loc = function
| AstHir.Watching(l, _, _) | AstHir.Emit(l, _) | AstHir.Await(l, _)
| AstHir.When(l, _, _)  | AstHir.Run(l, _, _) | AstHir.Par(l, _, _)
| AstHir.DeclSignal(l, _)  | AstHir.Skip (l)  | AstHir.Return (l,_)
| AstHir.Invoke (l,_,_,_) | AstHir.Block (l, _) | AstHir.If (l,_,_,_)
| AstHir.DeclVar (l,_,_,_,_) | AstHir.Seq (l,_,_) | AstHir.Assign (l,_,_)
| AstHir.While (l,_,_) | AstHir.Case (l,_,_) -> l

let degenerifyType (t: sailtype) (generics: (string * sailtype ) list) loc : sailtype result =
  let rec aux = function
  | Bool -> lift Bool
  | Int -> lift Int 
  | Float -> lift Float
  | Char -> lift Char
  | String -> lift String
  | ArrayType (t,s) -> let+ t = aux t in ArrayType (t, s)
  | CompoundType (_name, _tl)-> error [ loc ,"todo compoundtype"]
  | Box t -> let+ t = aux t in Box t
  | RefType (t,m) -> let+ t = aux t in RefType (t,m)
  | GenericType t when generics = [] -> error [loc,Printf.sprintf "generic type %s present but empty generics list" t]
  | GenericType n -> 
    begin
      match List.assoc_opt n generics with
      | Some GenericType t -> GenericType t |> lift
      | Some t -> aux t
      | None -> error [loc,Printf.sprintf "generic type %s not present in the generics list" n]
    end
  in
  aux t

(*todo : generalize*)
let type_of_binOp (op:binOp) (operands_type:sailtype) : sailtype = match op with
  | Lt | Le | Gt | Ge | Eq | NEq | And | Or -> Bool
  | Plus | Mul | Div | Minus | Rem -> operands_type

module Pass : Body with
              type in_body = Hir.statement and   
              type out_body = statement = 
struct
  type in_body = Hir.statement
  type out_body = statement

   
  let matchArgParam (l,arg: loc * sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: (string * sailtype ) list) : (sailtype * (string * sailtype ) list) result =
    let rec aux (a:sailtype) (m:sailtype) (g: (string * sailtype) list) = 
    match (a,m) with
    | Bool,Bool -> lift (Bool,g)
    | Int,Int -> lift (Int,g)
    | Float,Float -> lift (Float,g)
    | Char,Char -> lift (Char,g)
    | String,String -> lift (String,g)
    | ArrayType (at,s),ArrayType (mt,s') -> 
      if s = s' then
        let+ t,g = aux at mt g in ArrayType (t,s),g
      else
        error [l,Printf.sprintf "array length mismatch : wants %i but %i provided" s' s]
    | CompoundType _, CompoundType _ -> error [l, "todocompoundtype"]
    | Box _at, Box _mt -> error [l,"todobox"]
    | RefType (at,am), RefType (mt,mm) -> if am <> mm then error [l, "different mutability"] else aux at mt g
    | at,GenericType gt ->
     begin
        if List.mem gt generics then
          match List.assoc_opt gt g with
          | None -> lift (at,(gt,at)::g)
          | Some t -> if t = at then lift (at,g) else error [l,"generic type mismatch"]
        else
          error [l,Printf.sprintf "generic type %s not declared" gt]
      end
    | _ -> error [l,Printf.sprintf "wants %s but %s provided" 
           (string_of_sailtype (Some m_param))
           (string_of_sailtype (Some arg))]
    in aux arg m_param resolved_generics  


  let check_call (name:string) (args: expression list) (env:Pass.TypeEnv.t) loc : sailtype option result =
    match Pass.TypeEnv.get_function env (Method name)  with
    | Some (Method (_l,f)) -> 
      begin
        let nb_args = List.length args and nb_params = List.length f.args in

          let* _ = if nb_args <> nb_params then error [loc, Printf.sprintf "unexpected number of arguments passed to %s : expected %i but got %i" name nb_params nb_args] else lift () in
          let* resolved_generics = List.fold_left2 
          (
            fun g ca (_,a) ->
              let* g in 
              let+ x = matchArgParam (extract_exp_loc_ty ca) a f.generics g in
              snd x
          )  
          (lift [])
          args 
          f.args 
        in
        (* List.iter (fun (s,r) -> Printf.fprintf stdout "generic %s resolved to %s\n" s (string_of_sailtype (Some r)) ) resolved_generics; *)
        begin
          match f.ret with
          | Some r ->  let+ r = degenerifyType r resolved_generics loc in Some r
          | None -> lift None
        end
      end

    | None -> error [loc,"unknown method " ^ name]
    | _ -> error [loc,"problem with env"]

  let lower_expression (e : Hir.expression) (te: Pass.TypeEnv.t) (generics : string list): expression result = 
  let rec aux = function
    | AstHir.Variable (l,id) -> let+ _,(_,t) = Pass.TypeEnv.get_var te id l in AstHir.Variable((l,t),id)
    | AstHir.Deref (l,e) -> let* e = aux e in
      begin
        match e with
        | AstHir.Ref _ as t -> AstHir.Deref((l,extract_exp_loc_ty t |> snd), e) |> lift
        | _ -> error [l,"can't deref a non-reference!"]
      end

    | AstHir.ArrayRead (l,array_exp,idx) -> let* array_exp = aux array_exp and* idx = aux idx in
      begin 
        match extract_exp_loc_ty array_exp |> snd with
        | ArrayType (t,_) -> 
          let* _ = matchArgParam (extract_exp_loc_ty idx) Int generics [] in
          AstHir.ArrayRead((l,t),array_exp,idx) |> lift
        | _ -> error [l,"not an array !"]
      end

    | AstHir.StructRead (l,_struct_exp,_field) -> error [l,"todo: struct read"]
    | AstHir.Literal (l,li) -> let t = sailtype_of_literal li in AstHir.Literal((l,t),li) |> lift
    | AstHir.UnOp (l,op,e) -> let+ e = aux e in AstHir.UnOp ((l, extract_exp_loc_ty e |> snd),op,e)
    | AstHir.BinOp (l,op,le,re) ->  
      let* le = aux le and* re = aux re in
      let lt = extract_exp_loc_ty le  and rt = extract_exp_loc_ty re |> snd in
      let+ t = matchArgParam lt rt generics [] in
      let op_t = type_of_binOp op (fst t) in
      AstHir.BinOp ((l,op_t),op,le,re)

    | AstHir.Ref  (l,mut,e) -> let+ e = aux e in AstHir.Ref((l,RefType(extract_exp_loc_ty e |> snd,mut)),mut, e)
    | AstHir.ArrayStatic (l,el) -> 
      let* first_t = List.hd el |> aux  in
      let first_t = extract_exp_loc_ty first_t |> snd in
      let el,errors = partition_result (
        fun e -> let* t = aux e in
        if extract_exp_loc_ty t |> snd = first_t then lift t else error [l,"mixed type array"]
      ) el in 
      if errors = [] then
        let t = ArrayType (first_t, List.length el) in AstHir.ArrayStatic((l,t),el)  |> lift
      else
        Error errors

    | AstHir.StructAlloc (l,_name,_fields) -> error [l, "todo: struct alloc"]
    | AstHir.EnumAlloc (l,_name,_el) -> error [l, "todo: enum alloc"]

    in aux e


  let lower (decl:in_body declaration_type) env = 
    let open Common.Monad.MonadOperator(Common.MonadOption.M) in
    let rec aux s (te:Pass.TypeEnv.t) = match s with
      | AstHir.DeclVar (l, mut, id, t, (optexp : Hir.expression option)) -> 
        let optexp =  optexp  >>| fun e -> lower_expression e te decl.generics in 
        begin
          let* var_type =             
            match (t,optexp) with
            | (Some t,Some e) -> let* e in let tv = extract_exp_loc_ty e in let+ a = matchArgParam tv t decl.generics [] in fst a
            | (Some t, None) -> lift t
            | (None,Some t) -> let+ t in extract_exp_loc_ty t |> snd
            | (None,None) -> error [l,"can't infere type with no expression"]
            
          in 
          let* te' = Pass.TypeEnv.declare_var te id (l,(mut,var_type)) in 
          
          match optexp with
          | None -> (AstHir.DeclVar (l,mut,id,Some var_type,None),te') |> lift
          | Some e -> let+ e in AstHir.DeclVar (l,mut,id,Some var_type,Some e),te'
        end
        
      | AstHir.Assign(loc, e1, e2) -> 
        let* e1 = lower_expression e1 te decl.generics
        and* e2 = lower_expression e2 te decl.generics in
        let* _ = matchArgParam (extract_exp_loc_ty e1) (extract_exp_loc_ty e2 |> snd) [] [] in
        lift (AstHir.Assign(loc, e1, e2),te)

      | AstHir.Seq(loc, c1, c2) -> 
        let* c1,te1 = aux c1 te in
        let+ c2,te2 = aux c2 te1 in
        AstHir.Seq(loc, c1, c2) ,te2



      | AstHir.If(loc, cond_exp, then_s, else_s) -> 
        let* cond_exp = lower_expression cond_exp te decl.generics in
        let* _ = matchArgParam (extract_exp_loc_ty cond_exp) Bool [] [] in
        let* res,_ = aux then_s te in
        begin
        match else_s with
        | None -> lift (AstHir.If(loc, cond_exp, res, None),te)
        | Some s -> let+ s,_ = aux s te in (AstHir.If(loc, cond_exp, res, Some s),te)
        end

      | AstHir.While(loc,e,c) -> 
        let* e = lower_expression e te decl.generics in
        let+ t,_ = aux c te in
        AstHir.While(loc,e,t),te

      | AstHir.Case(loc, e, _cases) ->
        let+ e = lower_expression e te decl.generics in
        AstHir.Case (loc, e, []),te


      | AstHir.Invoke(loc, var, id, el) -> (* todo: handle var *)
        let el,errors = partition_result (fun e -> lower_expression e te decl.generics) el in
        
        if errors = [] then
          let+ _ = check_call id el env loc in
          AstHir.Invoke(loc, var, id,el),te
        else error errors

      | AstHir.Return(l, None) as r -> 
        if decl.ret = None then lift (r,te) else  error [l,"void return"]

      | AstHir.Return(l, Some e) ->
        if decl.bt <> Pass.BMethod then 
          error [l, Printf.sprintf "process %s : processes can't return non-void type" decl.name] 
        else
          begin
          match decl.ret with 
          | None -> error [l,"non-void return"] 
          | Some r ->
            let* e = lower_expression e te decl.generics in
            let+ _ = matchArgParam (extract_exp_loc_ty e) r decl.generics [] in
            AstHir.Return(l, Some e),te
          end

      | AstHir.Block (loc, c) -> 
        let+ res,te' = aux c (Pass.TypeEnv.new_frame te) in 
        AstHir.Block(loc,res),te'

      | AstHir.Skip (loc) -> lift (AstHir.Skip(loc),te)

      | s when decl.bt = Pass.BMethod -> error [extract_statements_loc s, Printf.sprintf "method %s : methods can't contain reactive statements" decl.name]


      | AstHir.Watching(loc, s, c) -> let+ res,_ = aux c te in AstHir.Watching(loc, s, res),te
      | AstHir.Emit(loc, s) -> lift (AstHir.Emit(loc,s),te)
      | AstHir.Await(loc, s) -> lift (AstHir.When(loc, s, AstHir.Skip(loc)),te)
      | AstHir.When(loc, s, c) -> let+ res,_ = aux c te in AstHir.When(loc, s, res),te
      | AstHir.Run(loc, id, el) ->
        let el,errors = partition_result (fun e -> lower_expression e te decl.generics) el in
        if errors = [] then
          let+ _ = check_call id el env loc in
          AstHir.Run(loc, id, el),te
        else error errors
      | AstHir.Par(loc, c1, c2) -> 
        let* c1,te1 = aux c1 te in
        let+ c2,te2 = aux c2 te1 in
        AstHir.Par(loc, c1, c2),te2
      | AstHir.DeclSignal(loc, s) -> lift (AstHir.DeclSignal(loc, s),te)


    in 
    let+ res,_ = aux decl.body env in res
end