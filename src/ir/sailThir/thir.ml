
open Common
open TypesCommon
open Parser
open IrHir


let extract_type = function
| AstThir.Variable (_,t,_) | AstThir.Deref (_,t,_) | AstThir.StructRead (_,t,_,_)
| AstThir.ArrayRead (_,t,_,_) | AstThir.Literal (_,t,_) | AstThir.UnOp (_,t,_,_)
| AstThir.BinOp (_,t,_,_,_) | AstThir.Ref  (_,t,_,_) | AstThir.ArrayStatic (_,t,_)
| AstThir.StructAlloc (_,t,_,_) | AstThir.EnumAlloc  (_,t,_,_) | AstThir.MethodCall (_,t,_,_) -> t

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


  let rec matchArgParam (arg: sailtype) (m_param : sailtype) : sailtype =
    match (arg,m_param) with
    | Bool,Bool -> Bool
    | Int,Int -> Int
    | Float,Float -> Float
    | Char,Char -> Char
    | String,String -> String
    | ArrayType (at,s),ArrayType (mt,s') -> 
      if s = s' then
        let t = matchArgParam at mt in ArrayType (t,s)
      else
        Printf.sprintf "array length mismatch : wants %i but %i provided" s' s  |> failwith
    | CompoundType _, CompoundType _ -> failwith "todocompoundtype"
    | Box _at, Box _mt -> failwith "todobox"
    | RefType (at,am), RefType (mt,mm) -> if am <> mm then failwith "different mutability" else matchArgParam at mt
    | t,GenericType _ -> t
    | _ -> Printf.sprintf "wants %s but %s provided" 
           (string_of_sailtype (Some m_param))
           (string_of_sailtype (Some arg))
          |> failwith   


  let check_call (name:string) (args: AstThir.expression list) (env:Pass.TypeEnv.t) : sailtype option =
    match Pass.TypeEnv.get_function env (Method ()) name with
    | Some (Method f) -> 
      List.iter2 (
        fun a (_,p) -> matchArgParam (extract_type a) p |> ignore
      ) args f.args;
      f.ret
    | None -> "unknown method " ^ name |> failwith
    | _ -> failwith "problem with env"

  let translate_expression (e : AstParser.expression) (te: Pass.TypeEnv.t): AstThir.expression  = 
  let rec aux = function
    | AstParser.Variable (l,id) -> let t = Pass.TypeEnv.get_var te id in AstThir.Variable(l,t,id)
    | AstParser.Deref (l,e) -> let e = aux e in
      begin
        match e with
        | AstThir.Ref _ as t -> AstThir.Deref(l,extract_type t, e)
        | _ -> failwith "can't deref a non-reference!"
      end

    | AstParser.ArrayRead (l,array_exp,idx) -> let array_exp = aux array_exp  and idx = aux idx in
      begin 
        match extract_type array_exp with
        | ArrayType (t,_) -> 
          matchArgParam (extract_type idx) Int |> ignore;
          AstThir.ArrayRead(l,t,array_exp,idx)
        | _ -> failwith "not an array !"
      end

    | AstParser.StructRead (_l,_struct_exp,_field) -> failwith "todo: struct read"
    | AstParser.Literal (l,li) -> let t = sailtype_of_literal li in AstThir.Literal(l,t,li)
    | AstParser.UnOp (l,op,e) -> let e = aux e in AstThir.UnOp (l, extract_type e,op,e)
    | AstParser.BinOp (l,op,le,re) ->  let le = aux le and re = aux re in
      let lt = extract_type le and rt = extract_type re in
      let t = matchArgParam lt rt in
      let op_t = type_of_binOp op t in
      AstThir.BinOp (l,op_t,op,le,re)
      
    | AstParser.Ref  (l,mut,e) -> let e = aux e in AstThir.Ref(l,RefType(extract_type e,mut),mut, e)
    | AstParser.ArrayStatic (l,el) -> 
      let first_t = List.hd el |> aux |> extract_type in
      let el = List.map (
        fun e -> let t = aux e in
        if extract_type t = first_t then t else failwith "mixed type array"
      ) el in 
      let t = ArrayType (first_t, List.length el) in AstThir.ArrayStatic(l,t,el) 

    | AstParser.StructAlloc (_l,_name,_fields) -> failwith "todo: struct alloc"
    | AstParser.EnumAlloc (_l,_name,_el) -> failwith "todo: enum alloc"
    | AstParser.MethodCall (l,name,args) -> 
      let args = List.map (fun e -> aux e) args in
      match check_call name args te with
      | None -> failwith "trying to use the result of void method"
      | Some t -> AstThir.MethodCall(l, t, name, args)
    in aux e


  let translate c env  = 
    let open Option.MonadOption in
    let rec aux s (te:Pass.TypeEnv.t) = match s with
      | AstHir.DeclVar (loc, mut, id, t, optexp ) -> 
        let optexp = optexp >>| fun e -> translate_expression e te in 
        begin
          let var_type = 
          match (t,optexp) with
          | (Some t,Some e) -> let tv = extract_type e in matchArgParam t tv
          | (Some t, None) -> t
          | (None,Some t) -> extract_type t
          | (None,None) -> failwith "can't infere type with no expression"
          in
          let te' = Pass.TypeEnv.declare_var te id var_type in 
          AstHir.DeclVar (loc,mut,id,t,optexp),te'
        end
      | AstHir.DeclSignal(loc, s) -> AstHir.DeclSignal(loc, s),te
      | AstHir.Skip (loc) -> AstHir.Skip(loc),te
      | AstHir.Assign(loc, e1, e2) -> 
        let e1 = translate_expression e1 te
        and e2 = translate_expression e2 te in
        matchArgParam (extract_type e1) (extract_type e2) |> ignore;
        AstHir.Assign(loc, e1, e2),te

      | AstHir.Seq(loc, c1, c2) -> 
        let c1,te1 = aux c1 te in
        let c2,te2 = aux c2 te1 in
        AstHir.Seq(loc, c1, c2) ,te2

      | AstHir.Par(loc, c1, c2) -> 
        let c1,te1 = aux c1 te in
        let c2,te2 = aux c2 te1 in
        AstHir.Par(loc, c1, c2),te2

      | AstHir.If(loc, cond_exp, then_s, else_s) -> 
        let cond_exp =  translate_expression cond_exp te in
        let else_s = else_s >>| fun s -> aux s te |> fst in 
        matchArgParam (extract_type cond_exp) Bool |> ignore;
        AstHir.If(loc, cond_exp, aux then_s te |> fst, else_s),te


      | AstHir.While(loc,e,c) -> AstHir.While(loc, translate_expression e te, aux c te |> fst),te
      | AstHir.Case(loc, e, _cases) -> AstHir.Case (loc, translate_expression e te, []),te
      | AstHir.Invoke(loc, ign, id, el) -> 
        let el = List.map (fun e -> translate_expression e te) el in
        (* fixme : need to add externals :  check_call id el decls |> ignore; *)
        AstHir.Invoke(loc, ign, id,el),te

      | AstHir.Return(_, None) as r -> r,te
      | AstHir.Return(loc, Some e) -> AstHir.Return(loc, Some (translate_expression e te)),te
      | AstHir.Run(loc, id, el) ->
        let el = List.map (fun e -> translate_expression e te) el in
         AstHir.Run(loc, id, el),te

      | AstHir.Emit(loc, s) -> AstHir.Emit(loc,s),te
      | AstHir.Await(loc, s) -> AstHir.When(loc, s, AstHir.Skip(loc)),te
      | AstHir.When(loc, s, c) -> AstHir.When(loc, s, aux c te |> fst),te
      | AstHir.Watching(loc, s, c) -> AstHir.Watching(loc, s, aux c te  |> fst),te
      | AstHir.Block (loc, c) -> 
        let c,te' = aux c (Pass.TypeEnv.new_frame te) in
        AstHir.Block(loc,c),te'
    in 
    aux c env |> fst
end