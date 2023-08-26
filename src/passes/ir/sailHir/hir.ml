open SailParser
open Common
open TypesCommon
open Monad
open AstHir
open HirUtils
open M
type expression = HirUtils.expression
type statement = HirUtils.statement


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
    
    let rec aux (info,s : m_in) : m_out M.ECS.t = 
    
      let buildSeq s1 s2 = {info; stmt = Seq (s1, s2)} in 
      let buildStmt stmt = {info;stmt} in
      let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

      match s with
      | DeclVar (mut, id, t, e ) -> 
        M.ECS.set_var info id >>= fun () ->
        let* t = match t with 
          | None -> return None 
          | Some t ->       
            let* (ve,d) = M.ECS.get in 
            let* t',d' = (follow_type t d) |> M.EC.lift |> M.ECS.lift in 
            let+ () = M.ECS.update (fun _ -> M.E.pure (ve,d') |> M.EC.lift ) in
            Some t'
        in 
        begin match e with 
          | Some e -> let+ (e, s) = lower_expression e in
            buildSeqStmt s (DeclVar (mut,id, t, Some e))
          | None -> return {info;stmt=DeclVar (mut,id, t, None)}
        end 
      | Skip -> return {info;stmt=Skip}
      | Assign(e1, e2) ->  
          let* e1,s1 = lower_expression e1 in
          let+ e2,s2 = lower_expression e2 in
          buildSeq s1 @@ buildSeqStmt s2 @@ Assign (e1, e2)

      | Seq (c1, c2) -> let+ c1 = aux c1 and* c2 = aux c2 in {info;stmt=Seq (c1, c2)}
      | If (e, c1, Some c2) -> 
        let+ e,s = lower_expression e and* c1 = aux c1 and* c2 = aux c2 in 
        buildSeqStmt s (If (e, c1, Some c2))

      | If ( e, c1, None) -> 
          let+ (e, s) = lower_expression e and* c1 = aux c1 in 
          buildSeqStmt s (If (e, c1, None))
          
      | While (e, c) -> 
        let+ e,s = lower_expression e and* c = aux c in
        let c = buildStmt (If (e,c,Some (buildStmt Break))) in 
        buildSeqStmt s (Loop c)

      | Loop c -> let+ c = aux c in 
        buildStmt (Loop c)

      | For {var;iterable;body} ->  
        begin
        match iterable with 
        | _,ArrayStatic el ->
          let open AstParser in 
          let arr_id = "_for_arr_" ^ var in 
          let i_id = "_for_i_" ^ var in 
          let arr_length = List.length el in 

          let tab_decl = info,DeclVar (false, arr_id, Some (dummy_pos,ArrayType ((dummy_pos,Int 32),arr_length)), Some iterable) in
          let var_decl = info,DeclVar (true, var, Some (dummy_pos,Int 32), None) in 
          let i_decl = info,DeclVar (true, i_id, Some (dummy_pos,Int 32), Some (info,(Literal (LInt {l=Z.zero;size=32})))) in 

          let tab = info,Variable arr_id in 
          let var = info,Variable var in
          let i = info,Variable i_id in
          
          let cond = info,BinOp (Lt, i, (info,Literal (LInt {l=Z.of_int arr_length;size=32}))) in 
          let incr = info,Assign (i,(info,BinOp (Plus, i, (info, Literal (LInt {l=Z.one;size=32}))))) in
          let init = info,Seq ((info,Seq (tab_decl,var_decl)), i_decl) in 
          let vari = info, Assign (var,(info,ArrayRead(tab,i))) in 

          let body = info,Seq((info,Seq(vari,body)),incr) in
          let _while = info,While (cond,body) in 
          let _for = info,Seq(init,_while) in 
          aux _for
        | loc,_ -> M.ECS.throw Logging.(make_msg loc "for loop only allows a static array expression at the moment")
        end

      | Break () -> return {info; stmt=Break}
  (*   | Case(loc, e, cases) -> Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
      | Case (e, _cases) ->  let+ e,s = lower_expression e in
          buildSeqStmt s (Case (e, []))

      | Invoke (mod_loc, id, args) ->
          let+ args,s = ListM.map lower_expression args in
          buildSeqStmt s (Invoke {ret_var=None;import=mod_loc;id;args})

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
    M.E.(bind (M.run aux env body) (fun (r,venv) -> pure (r,venv,tenv))) |> M.E.recover ({info=dummy_pos;stmt=Skip},snd env,tenv)


  let lower_process (p:p_in process_defn) ((env,decls),tenv: HIREnv.t * _ ) sm : (p_out * HIREnv.D.t * _) M.E.t = 
    let open AstParser in 
    let module F = MonadFunctions(M) in
    let open UseMonad(E) in
    
    let params = List.to_seq p.p_interface.p_params |> Seq.map (fun (p:param) -> p.id,p.loc) |> FieldMap.of_seq  in
    let locals = List.to_seq p.p_body.locals |> Seq.map (fun ((l,id),_) -> id,l ) |> FieldMap.of_seq  in 
    let read,write = p.p_interface.p_shared_vars in
    let read = List.to_seq read |> Seq.map (fun (l,(id,_)) -> id,l) |> FieldMap.of_seq in
    let write = List.to_seq write |> Seq.map (fun (l,(id,_)) -> id,l) |> FieldMap.of_seq in


    let union_no_dupl = FieldMap.union (fun _k _loca _locb -> None) in 
    let has_name_conflict = FieldMap.(
      union_no_dupl params locals |> union_no_dupl read |> union_no_dupl write |> cardinal 
      <> 
      cardinal params + cardinal locals + cardinal read + cardinal write
    ) in 
    E.throw_if Logging.(make_msg dummy_pos @@ Fmt.str "process '%s' : name conflict between params,local decls or shared variables" p.p_name) has_name_conflict 
    >>= fun () ->

    let add_locals v e = ListM.fold_left (fun e ((l,id),_) -> HIREnv.declare_var id (l,()) e) (e,decls) v >>| fst in 
    let add_rw r e = ListM.fold_left (fun e (l,(id,_)) -> HIREnv.declare_var id (l,()) e) (e,decls) r >>| fst in 

    let* env = add_locals p.p_body.locals env >>= add_rw (fst p.p_interface.p_shared_vars) >>= add_rw (snd p.p_interface.p_shared_vars) in


    let* init,decls,tenv = lower_method (p.p_body.init,()) ((env,decls),tenv) sm |> E.recover ({info=dummy_pos;stmt=Skip},decls,tenv) in
    
    let* (proc_init,_),decls = F.ListM.map (fun ((l,p): loc * _ proc_init) ->
      let open UseMonad(M) in 
      let+ params = F.ListM.map lower_expression p.params in l,{p with params}
    ) p.p_body.proc_init (env,decls) |> M.ECS.run 
    in 
    let+ loop = 
      let process_cond = function None -> return None | Some c -> let+ (cond,_),_ = lower_expression c (env,decls) |> M.ECS.run in Some cond in
      let rec aux (l,s) = match s with
      | Statement (s,cond) -> let+ s,_,_ = lower_method (s,()) ((env,decls),tenv) sm and* cond = process_cond cond in l,Statement (s,cond)
      | Run (proc,cond) -> let+ cond = process_cond cond in l,Run (proc,cond)
      | PGroup g -> 
        let* cond = process_cond g.cond in
        let+ children = ListM.map aux g.children in
        l,PGroup {g with cond ; children}
      in aux p.p_body.loop
    in
  {p.p_body with init ; proc_init; loop},decls,tenv

  end
)