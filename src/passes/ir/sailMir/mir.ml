open AstMir
open Common 
open TypesCommon
open Monad
open MirMonad
open MirUtils
open IrThir
open IrHir
open SailParser
open UseMonad(M)


open Pass

module Pass = MakeFunctionPass(V)(
struct
  let name = "MIR"
  
  type m_in = Thir.statement
  type m_out = mir_function
  type p_in =  (HirUtils.statement,HirUtils.expression) AstParser.process_body
  type p_out = p_in

  let rec lexpr (e : Thir.expression) : expression M.t = 
    let open AstHir in
    let lt = e.info in 
    match e.exp with 
      | Variable name ->
        let* id = find_scoped_var name in
        let+ () = M.update_var (fst lt) id assign_var in buildExp lt (Variable id)
      | Deref e -> rexpr e 
      | ArrayRead (e1, e2) -> let+ e1' = lexpr e1 and* e2' = rexpr e2 in buildExp lt (ArrayRead(e1',e2'))
      | StructRead (origin,e,field) -> let+ e = lexpr e in buildExp lt (StructRead (origin,e,field))
      | Ref _ -> M.error @@ Error.make (fst lt) "todo"
      |  _ ->  M.error @@ Error.make (fst lt) @@ "thir didn't lower correctly this expression" 
  and rexpr (e : Thir.expression) : expression M.t = 
    let lt = e.info in 
    let open AstHir in
    match e.exp with 
      | Variable name ->
        let+ id = find_scoped_var name in buildExp lt (Variable id)
      | Literal l -> buildExp lt (Literal l) |> M.pure
      | Deref e -> lexpr e 
      | ArrayRead (array_exp,idx) -> let+ arr = rexpr array_exp and* idx' = rexpr idx in buildExp lt (ArrayRead(arr,idx'))
      | UnOp (o, e) -> let+ e' = rexpr e in buildExp lt (UnOp (o, e'))
      | BinOp (o ,e1, e2) ->  let+ e1' = rexpr e1 and* e2' = rexpr e2 in buildExp lt (BinOp(o, e1', e2'))
      | Ref (b, e) -> let+ e' = rexpr e in buildExp lt (Ref(b, e'))
      | ArrayStatic el -> let+ el' = ListM.map rexpr el in buildExp lt (ArrayStatic el')
      | StructRead (origin,struct_exp,field)  -> 
        let+ exp = rexpr struct_exp in 
        buildExp lt (StructRead (origin,exp,field))  
      
      | StructAlloc (origin,id, fields) -> 
        let+ fields = ListM.map (pairMap2 (rexpr)) fields in 
        buildExp lt (StructAlloc(origin,id,fields))
      | MethodCall _ 
      | _ ->  M.error @@ Error.make (fst lt) @@ "thir didn't lower correctly this expression" 



      open UseMonad(M.E)   


  let lower_method (body,_ : m_in * method_sig) env (_sm: (m_in,p_in) SailModule.methods_processes SailModule.t) : (m_out * SailModule.DeclEnv.t) M.E.t =
    let rec aux (s : Thir.statement) : m_out M.t = 
      let open UseMonad(M) in
      let loc = s.info in
      match s.stmt with
      | DeclVar(mut, id, Some ty, None) -> 
        let* bb = emptyBasicBlock loc  in
        let* id = M.fresh_scoped_var >>| get_scoped_var id in
        let+ () = M.declare_var loc id {ty;mut;id;loc} in
        [{location=loc; mut; id; varType=ty}],bb

      | DeclVar(mut, id, Some ty, Some e) -> 
        let* expression = rexpr e in
        let* id = M.fresh_scoped_var >>| get_scoped_var id in
        let* () = M.declare_var loc id {ty;mut;id;loc} in
        let target = AstHir.buildExp (loc,ty) (Variable id) in
        let+ bn = assignBasicBlock loc {location=loc; target; expression }  in
        [{location=loc; mut; id=id; varType=ty}],bn
        (* ++ other statements *)

      | DeclVar (_,name,None,_) -> failwith @@ "thir broken : variable declaration should have a type : " ^name

      | Skip -> let+ bb = emptyBasicBlock loc in ([],  bb)

      | Assign (e1, e2) -> 
        let* expression = rexpr e2 and* target = lexpr e1 in
        let+ bb = assignBasicBlock loc {location=loc; target; expression} in [],bb
        
      | Seq (s1, s2) ->
        (* let* env = M.get_env in *)
        let* d1, cfg1 = aux s1 
        and* d2, cfg2 = aux s2 in
        (* let* () = M.set_env env in  *)
        let+ bb = buildSeq cfg1 cfg2 in d1@d2,bb

      | If (e, s, None) -> 
        let* e' = rexpr e in
        let* d, cfg = aux s in
        let+ ite = buildIfThen loc e' cfg in
        (d,ite) 
        
      | If (e, s1, Some s2) -> 
        let* e' = rexpr e in
        let* d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        let+ ite = buildIfThenElse loc e' cfg1 cfg2 in
        (d1@d2, ite) 

      | Loop s ->  
        let* d, cfg = aux s in 
        let+ l = buildLoop loc cfg in
        (d, l)

      | Break -> 
        let* env = M.get_env in 
        let bb = {location=loc; forward_info=env; backward_info = (); assignments=[]; predecessors=LabelSet.empty;terminator=Some Break} in
        let+ cfg = singleBlock bb in
        ([],cfg)
        
      | Invoke (target, ((_,mname) as origin), (l,id), el) -> 
        let* ((_,realname),_) = M.throw_if_none (Error.make loc @@ Fmt.str "Compiler Error : function '%s' must exist" id) 
                                              (SailModule.DeclEnv.find_decl id (Specific (mname,Method)) (snd env))
        in
        let* el' = ListM.map rexpr el in
        let+ invoke = buildInvoke loc origin (l,realname) target el' in
        ([], invoke)

      | Return e ->
        let* e = match e with 
        | None -> None |> M.pure 
        | Some e -> let+ e' = rexpr e in Some e' in 
        let+ ret =  buildReturn loc e in
        ([], ret)

      | Case _ -> M.error @@ Error.make loc "unimplemented"

      | Block s -> 
        let* env = M.get_env in
        let* res = aux s in
        let+ () = M.set_env env in
        res

    in 
    let+ res = M.run aux body (fst env) in 
    res,(snd env)

    let preprocess = Error.Logger.pure

    let lower_process (c:p_in process_defn) env _ = M.E.pure (c.p_body,snd env)
  end
)
