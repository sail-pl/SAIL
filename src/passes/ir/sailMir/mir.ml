open MirAst
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
  
  type m_in = ThirUtils.statement
  type m_out = mir_function
  type p_in =  (HirUtils.statement,HirUtils.expression) AstParser.process_body
  type p_out = p_in

  let rec lexpr (exp : ThirUtils.expression) : expression M.t = 
    let open IrAst.Ast in
    match exp.node with 
      | Variable name ->
        let* id = find_scoped_var name in
        let+ () = M.update_var exp.tag.loc  id assign_var in buildExp exp.tag (Variable id)
      | Deref e -> rexpr e 
      | ArrayRead a -> let+ array = lexpr a.array and* idx = rexpr a.idx in
        buildExp exp.tag (ArrayRead {array;idx})

      | StructRead2 s -> let+ strct = lexpr s.value.strct in buildExp exp.tag (StructRead2 {s with value={s.value with strct}})

      | Ref _ -> M.error Logging.(make_msg exp.tag.loc "todo")

      | Literal _ | UnOp _ | BinOp _  | ArrayStatic _ | StructAlloc2 _ | EnumAlloc _ ->
      M.error Logging.(make_msg exp.tag.loc  @@ "compiler error : not a lexpr")

  and rexpr (exp : ThirUtils.expression) : expression M.t = 
  let open IrAst.Ast in
    match exp.node with 
      | Variable name ->
        let+ id = find_scoped_var name in buildExp exp.tag (Variable id)
      | Literal l -> buildExp exp.tag (Literal l) |> M.pure
      | Deref e -> lexpr e 
      | ArrayRead a -> let+ array = rexpr a.array and* idx = rexpr a.idx in buildExp exp.tag (ArrayRead {array;idx})
      | UnOp (o, e) -> let+ e' = rexpr e in buildExp exp.tag (UnOp (o, e'))
      | BinOp bop ->  let+ left = rexpr bop.left and* right = rexpr bop.right in buildExp exp.tag (BinOp {bop with left;right})
      | Ref (b, e) -> let+ e' = rexpr e in buildExp exp.tag (Ref(b, e'))
      | ArrayStatic el -> let+ el' = ListM.map rexpr el in buildExp exp.tag (ArrayStatic el')
      | StructRead2 s  -> 
        let+ strct = rexpr s.value.strct in 
        buildExp exp.tag (StructRead2 {s with value={s.value with strct}})  
      
      | StructAlloc2 s -> 
        let+ fields = ListM.map (fun f -> pairMap2 (fun f ->  let+ value = rexpr f.value in {f with value}) f)  s.value.fields in 
        buildExp exp.tag (StructAlloc2 {s with value={s.value with fields}})
      | EnumAlloc _ ->  M.error @@ Logging.(make_msg exp.tag.loc @@ "compiler error : not a rexpr")


      open UseMonad(M.E)   


  let lower_method (body,_ : m_in * method_sig) (env,tenv) (_sm: (m_in,p_in) SailModule.methods_processes SailModule.t) : (m_out * SailModule.DeclEnv.t * _) M.E.t =
    let rec aux (s : ThirUtils.statement) : m_out M.t = 
      let open UseMonad(M) in
      let loc = s.tag.loc in
      match s.node with
      | DeclVar2 d -> 
        let* bb = emptyBasicBlock loc  in
        let* id = M.fresh_scoped_var >>| get_scoped_var d.id in
        let+ () = M.declare_var loc id {ty=d.ty;mut=d.mut;id;loc} in
        [{location=loc; mut=d.mut; id; varType=d.ty}],bb

      | Skip -> let+ bb = emptyBasicBlock loc in ([],  bb)

      | Assign a -> 
        let* expression = rexpr a.value and* target = lexpr a.path in
        let+ bb = assignBasicBlock loc {location=loc; target; expression} in [],bb
        
      | Seq (s1, s2) ->
        (* let* env = M.get_env in *)
        let* d1, cfg1 = aux s1 
        and* d2, cfg2 = aux s2 in
        (* let* () = M.set_env env in  *)
        let+ bb = buildSeq cfg1 cfg2 in d1@d2,bb

      | If ({else_=None;_} as if_) -> 
        let* cond = rexpr if_.cond in
        let* d, cfg = aux if_.then_ in
        let+ ite = buildIfThen loc cond cfg in
        (d,ite) 
        
      | If ({else_=Some else_;_} as if_) -> 
        let* cond = rexpr if_.cond in
          let* d1,cfg1 = aux if_.then_ and* d2,cfg2 = aux else_ in
        let+ ite = buildIfThenElse loc cond cfg1 cfg2 in
        (d1@d2, ite) 

      | Loop s ->  
        let* d, cfg = aux s in 
        let+ l = buildLoop loc cfg in
        (d, l)

      | Break -> 
        let* env,_ = M.get_env in 
        let bb = {location=loc; forward_info=env; backward_info = (); assignments=[]; predecessors=LabelSet.empty;terminator=Some Break} in
        let+ cfg = singleBlock bb in
        ([],cfg)
        
      | Invoke2 i -> 
        let* (realname,_) = M.throw_if_none Logging.(make_msg loc @@ Fmt.str "Compiler Error : function '%s' must exist" i.value.id.value) 
                                              (SailModule.DeclEnv.find_decl i.value.id.value (Specific (i.import.value,Method)) (snd env))
        in
        let* args = ListM.map rexpr i.value.args in
        let+ invoke = buildInvoke loc i.import (mk_locatable i.value.id.loc realname.value) i.value.ret_var args in
        ([], invoke)

      | Return e ->
        let* e = match e with 
        | None -> None |> M.pure 
        | Some e -> let+ e' = rexpr e in Some e' in 
        let+ ret =  buildReturn loc e in
        ([], ret)

      | Case _ -> M.error Logging.(make_msg loc "unimplemented")

      | Block s -> 
        let* env = M.get_env in
        let* res = aux s in
        let+ () = M.set_env env in
        res

    in 
    let+ res = M.run aux body (fst env,tenv) in 
    res,(snd env),tenv

    let preprocess = Logging.Logger.pure

    let lower_process (c:p_in process_defn) ((_,env),tenv) _ = M.E.pure (c.p_body,env,tenv)
  end
)
