open SailParser
open Common
open TypesCommon
open Monad
open IrAst
open HirUtils
open M


module Pass = Pass.MakeFunctionPass (V)(
struct
  let name = "HIR"

  type m_in = AstParser.statement
  type m_out = statement

  type p_in = (m_in,AstParser.expression) AstParser.process_body
  type p_out = (m_out,expression) AstParser.process_body
      
  open UseMonad(M)
  open MakeOrderedFunctions(String)

  (* let get_hint id env = 
    Option.bind (List.nth_opt (HIREnv.get_closest id env) 0) (fun id -> Some (None,Printf.sprintf "Did you mean %s ?" id)) *)

  let preprocess = resolve_names

  let lower_method (body,_) (env,tenv:HIREnv.t * _) _ : (m_out * HIREnv.D.t * _) M.E.t = 
    let open MonadSyntax(M.ECS) in
    let open MonadOperator(M.ECS) in 
    
    let rec aux (stmt:m_in) : m_out M.ECS.t = 
    
      let buildSeq = Ast.buildSeq stmt.loc in
      let buildStmt = Ast.buildStmt stmt.loc in
      let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

      match stmt.value with
      | DeclVar (mut, id, t, e ) -> 
        M.ECS.set_var stmt.loc id >>= fun () ->
        let* ty = match t with 
          | None -> return None 
          | Some t ->       
            let* (ve,d) = M.ECS.get in 
            let* t',d' = (follow_type t d) |> M.EC.lift |> M.ECS.lift in 
            let+ () = M.ECS.update (fun _ -> M.E.pure (ve,d') |> M.EC.lift ) in
            Some t'
        in 
        begin match e with 
          | Some e -> let+ (e, s) = lower_expression e in
            buildSeqStmt s (DeclVar {mut;id;ty;value=Some e})
          | None -> return (buildStmt (DeclVar {mut;id;ty;value=None}))
        end 

      | Skip -> return (buildStmt Skip)

      | Assign a ->  
        let+ path,s1 = lower_expression a.path 
        and* value,s2 = lower_expression a.value in
        buildSeq s1 @@ buildSeqStmt s2 @@ Assign {path; value}

      | Seq (c1, c2) -> 
        (buildSeq <$> aux c1) <*> aux c2 

      | If (e, then_, else_) -> 
        let+ cond,s = lower_expression e 
        and* then_ = aux then_ 
        and* else_ = match else_ with None -> return None | Some else_ -> aux else_ >>| Option.some in 
        buildSeqStmt s (If {cond;then_;else_})
          
      | While (e, c) -> 
        let+ cond,s = lower_expression e 
        and* then_ = aux c in
        let c = buildStmt (If {cond;then_;else_=Some (buildStmt Break)}) in 
        buildSeqStmt s (Loop c)

      | Loop c -> let+ c = aux c in 
        buildStmt (Loop c)

      | For {var;iterable;body} ->  (* fixme : temporary *)
        begin
        match iterable.value with 
        | ArrayStatic el ->
          let open AstParser in 
          let arr_id = "_for_arr_" ^ var in 
          let i_id = "_for_i_" ^ var in 
          let arr_length = List.length el in 
          let loc x = mk_locatable iterable.loc x in 
 
          let tab_decl = loc @@ DeclVar (false, arr_id, Some (loc @@ ArrayType (loc (Int 32),arr_length)), Some iterable) in
          let var_decl = loc @@ DeclVar (true, var, Some (loc @@ Int 32), None) in 
          let i_decl = loc @@ DeclVar (true, i_id, Some (loc @@ Int 32), Some (mk_locatable dummy_pos @@ (Literal (LInt {l=Z.zero;size=32})))) in 

          let tab = loc (Variable arr_id) in 
          let var = loc (Variable var) in
          let i =loc (Variable i_id) in
          
          let cond = loc @@ BinOp (Lt, i, (mk_locatable dummy_pos @@ Literal (LInt {l=Z.of_int arr_length;size=32}))) in 
          let incr = loc @@ Assign {path=i;value= loc @@ BinOp (Plus, i, (loc @@ Literal (LInt {l=Z.one;size=32})))} in
          let init = loc @@ Seq (loc @@ Seq (tab_decl,var_decl), i_decl) in 
          let vari = loc @@ Assign {path=var;value=loc @@ ArrayRead(tab,i)} in 

          let body = loc @@ Seq(loc @@ Seq(vari,body),incr) in
          let _while = loc @@ While (cond,body) in 
          let _for = loc @@ Seq(init,_while) in 
          aux _for
        | _ -> M.ECS.throw Logging.(make_msg iterable.loc "for loop only allows a static array expression at the moment")
        end

      | Break () -> return (buildStmt Break)

  (*   | Case(loc, e, cases) -> Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
      | Case (e, cases) ->  
          let open MonadFunctions(M.ECS) in
          let+ switch,s = lower_expression e
          and* _cases = ListM.map (pairMap2 aux) cases in
          buildSeqStmt s (Case {switch;cases=[]})

      | Invoke (mod_loc, id, args) ->
          let+ args,s1 = ListM.map lower_expression args in
          let s2 = Ast.Invoke (mk_importable mod_loc Ast.{ret_var=None;id;args}) in
          buildSeqStmt s1 s2

      | Return e -> 
          begin match e with 
          | None -> return @@ buildStmt (Return None)
          | Some e -> let+ e,s = lower_expression e in
            buildSeqStmt s (Return (Some e))
          end
      | Block c -> 
        let* () = M.ECS.update (fun e -> M.EC.pure (HIREnv.new_frame e)) in 
        let* c = aux c in 
        let+ () = M.ECS.update (fun e -> M.EC.pure (HIREnv.pop_frame e)) in
        buildStmt (Block c)
    


    in
    M.E.(bind (M.run aux env body) (fun (r,venv) -> pure (r,venv,tenv))) |> M.E.recover (MonoidSeq.mempty,snd env,tenv)


  let lower_process (p:p_in process_defn) ((env,decls),tenv: HIREnv.t * _ ) sm : (p_out * HIREnv.D.t * _) M.E.t = 
    let open AstParser in 
    let module F = MonadFunctions(M) in
    let open UseMonad(E) in
    
    let params = List.to_seq p.p_interface.p_params |> Seq.map (fun (p:param) -> p.id,p.loc) |> FieldMap.of_seq  in
    let locals = List.to_seq p.p_body.locals |> Seq.map (fun (id,_) -> id.value,id.loc ) |> FieldMap.of_seq  in 
    let read,write = p.p_interface.p_shared_vars in
    let read = List.to_seq read |> Seq.map (fun r -> fst r.value,r.loc) |> FieldMap.of_seq in
    let write = List.to_seq write |> Seq.map (fun w -> fst w.value,w.loc)  |> FieldMap.of_seq in


    let union_no_dupl = FieldMap.union (fun _k _loca _locb -> None) in 
    let has_name_conflict = FieldMap.(
      union_no_dupl params locals |> union_no_dupl read |> union_no_dupl write |> cardinal 
      <> 
      cardinal params + cardinal locals + cardinal read + cardinal write
    ) in 
    E.throw_if Logging.(make_msg dummy_pos @@ Fmt.str "process '%s' : name conflict between params,local decls or shared variables" p.p_name) has_name_conflict 
    >>= fun () ->

    let add_locals v e = ListM.fold_left (fun e (id,_) -> HIREnv.declare_var id.value (id.loc,()) e) (e,decls) v >>| fst in 
    let add_rw r e = ListM.fold_left (fun e rw -> HIREnv.declare_var (fst rw.value) (rw.loc,()) e) (e,decls) r >>| fst in 

    let* env = add_locals p.p_body.locals env >>= add_rw (fst p.p_interface.p_shared_vars) >>= add_rw (snd p.p_interface.p_shared_vars) in


    let* init,decls,tenv = lower_method (p.p_body.init,()) ((env,decls),tenv) sm |> E.recover (MonoidSeq.mempty,decls,tenv) in
    
    let* (proc_init,_),decls = F.ListM.map (fun (p : _ proc_init locatable) ->
      let open UseMonad(M) in 
      let+ params = F.ListM.map lower_expression p.value.params in 
      mk_locatable p.loc {p.value with params}
    ) p.p_body.proc_init (env,decls) |> M.ECS.run 
    in 
    let+ loop = 
      let process_cond = function None -> return None | Some c -> let+ (cond,_),_ = lower_expression c (env,decls) |> M.ECS.run in Some cond in
      let rec aux (stmt :(m_in, AstParser.expression) SailParser.AstParser.p_statement) = match stmt.value with
      | Statement (s,cond) -> 
        let+ s,_,_ = lower_method (s,()) ((env,decls),tenv) sm 
        and* cond = process_cond cond in 
        mk_locatable stmt.loc (Statement (s,cond))

      | Run (proc,cond) -> let+ cond = process_cond cond in mk_locatable stmt.loc @@ Run (proc,cond)
      | PGroup g -> 
        let* cond = process_cond g.cond in
        let+ children = ListM.map aux g.children in
        mk_locatable stmt.loc @@ PGroup {g with cond ; children}
      in aux p.p_body.loop
    in
  {p.p_body with init ; proc_init; loop},decls,tenv

  end
)