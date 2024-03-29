open SailParser
open Common
open TypesCommon
open Monad
open AstHir
open HirUtils
open M
module SM = SailModule
type expression = HirUtils.expression
type statement = HirUtils.statement


module Pass = Pass.MakeFunctionPass (V)(
struct
  let name = "HIR"

  type m_in = AstParser.statement
  type m_out = statement

  type p_in = (m_in,AstParser.expression) AstParser.process_body
  type p_out = (m_out,expression) AstParser.process_body
      
  open UseMonad(ECSW)
  open MakeOrderedFunctions(String)

  (* let get_hint id env = 
    Option.bind (List.nth_opt (HIREnv.get_closest id env) 0) (fun id -> Some (None,Printf.sprintf "Did you mean %s ?" id)) *)


  let lower_expression (e : AstParser.expression) : expression ECSW.t = 
    let open MonadSyntax(ECSW) in
    let rec aux (info,e : AstParser.expression) : expression ECSW.t  = 
    match e with 
      | Variable id -> 
        let* v = (ECS.find_var id |> ECSW.lift) in
        ECSW.throw_if_none Error.(make info @@ Fmt.str "undeclared variable '%s'" id)  v >>| fun _ ->
        {info; exp=Variable id}
      | Deref e -> 
        let+ e = aux e in {info;exp=Deref e}
      | StructRead (e, id) ->
        let+ e = aux e in {info; exp=StructRead (None, e, id)}
      | ArrayRead (e1, e2) ->
        let* e1 = aux e1 in 
        let+ e2 = aux e2 in 
        {info; exp=ArrayRead(e1,e2)}
      | Literal l -> return {info; exp=Literal l}
      | UnOp (op, e) -> 
        let+ e = aux e in {info;exp=UnOp (op, e)}
      | BinOp(op,e1,e2)->
        let* e1 = aux e1 in 
        let+ e2 = aux e2 in
        {info; exp=BinOp (op, e1, e2)}
      | Ref (b, e) ->
        let+ e = aux e in {info;exp=Ref(b, e)}
      | ArrayStatic el -> 
        let+ el = ListM.map aux el in {info;exp=ArrayStatic el}
      | StructAlloc (origin,id, m) ->
        let m' = List.sort_uniq (fun (id1,_) (id2,_) -> String.compare id1 id2) m in
        let* () = ECSW.throw_if (Error.make info "duplicate fields") List.(length m <> length m') in
        let+ m' = ListM.map (pairMap2 aux) m' in
        {info; exp=StructAlloc (origin, id, m')}

      | EnumAlloc (id, el) ->
        let+ el = ListM.map aux el in  {info;exp=EnumAlloc (id, el)}
      | MethodCall (mod_loc, id, el) ->
        let+ el = ListM.map aux el in {info ; exp=MethodCall(id, mod_loc, el)}
      in aux e

      
  let lower_method (body,_) (env:HIREnv.t) _ : (m_out * HIREnv.D.t) E.t = 
    let open MonadSyntax(ECS) in
    let open MonadOperator(ECS) in 
    
    let rec aux (info,s : m_in) : m_out ECS.t = 
    
      let buildSeq s1 s2 = {info; stmt = Seq (s1, s2)} in 
      let buildStmt stmt = {info;stmt} in
      let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

      match s with
      | DeclVar (mut, id, t, e ) -> 
        ECS.set_var info id >>= fun () ->
        let* t = match t with 
          | None -> return None 
          | Some t ->       
            let* (ve,d) = ECS.get in 
            let* t',d' = (follow_type t d) |> EC.lift |> ECS.lift in 
            let+ () = ECS.update (fun _ -> E.pure (ve,d') |> EC.lift ) in
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
          buildSeq s1 @@ buildSeqStmt s2 (Assign (e1, e2))

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

          let tab_decl = info,DeclVar (false, arr_id, Some (ArrayType (Int 32,arr_length)), Some iterable) in
          let var_decl = info,DeclVar (true, var, Some (Int 32), None) in 
          let i_decl = info,DeclVar (true, i_id, Some (Int 32), Some (info,(Literal (LInt {l=Z.zero;size=32})))) in 

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
        | loc,_ -> ECS.throw (Error.make loc "for loop only allows a static array expression at the moment")
        end

      | Break () -> return {info; stmt=Break}
  (*   | Case(loc, e, cases) -> Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
      | Case (e, _cases) ->  let+ e,s = lower_expression e in
          buildSeqStmt s (Case (e, []))

      | Invoke (mod_loc, lid, el) ->
          let+ el,s = ListM.map lower_expression el in
          buildSeqStmt s (Invoke(None, mod_loc, lid,el))

      | Return e -> 
          begin match e with 
          | None -> return @@ buildStmt (Return None)
          | Some e -> let+ e,s = lower_expression e in
            buildSeqStmt s (Return (Some e))
          end
      | Block c -> 
        let* () = ECS.update (fun e -> EC.pure (HIREnv.new_frame e)) in 
        let* c = aux c in 
        let+ () = ECS.update (fun e -> EC.pure (HIREnv.pop_frame e)) in
        buildStmt (Block c)
    


    in
    ECS.run (aux body env) |> E.recover ({info=dummy_pos;stmt=Skip},snd env)



  let lower_process (p:p_in process_defn) (env,decls:HIREnv.t) sm : (p_out * HIREnv.D.t) E.t = 
    let open AstParser in 
    let module F = MonadFunctions(ECSW) in
    let open UseMonad(E) in
    
    let params = List.to_seq p.p_interface.p_params |> Seq.map (fun (p:param) -> p.id,p.loc) |> FieldMap.of_seq  in
    let locals = List.to_seq p.p_body.locals |> Seq.map (fun (l,(id,_)) -> id,l ) |> FieldMap.of_seq  in 
    let read,write = p.p_interface.p_shared_vars in
    let read = List.to_seq read |> Seq.map (fun (l,(id,_)) -> id,l) |> FieldMap.of_seq in
    let write = List.to_seq write |> Seq.map (fun (l,(id,_)) -> id,l) |> FieldMap.of_seq in


    let union_no_dupl = FieldMap.union (fun _k _loca _locb -> None) in 
    let has_name_conflict = FieldMap.(
      union_no_dupl params locals |> union_no_dupl read |> union_no_dupl write |> cardinal 
      <> 
      cardinal params + cardinal locals + cardinal read + cardinal write
    ) in 
    E.throw_if Error.(make dummy_pos @@ Fmt.str "process '%s' : name conflict between params,local decls or shared variables" p.p_name) has_name_conflict 
    >>= fun () ->

    let add_locals v e = ListM.fold_left (fun e (l,(id,_)) -> HIREnv.declare_var id (l,()) e) (e,decls) v >>| fst in 
    let add_rw r e = ListM.fold_left (fun e (l,(id,_)) -> HIREnv.declare_var id (l,()) e) (e,decls) r >>| fst in 

    let* env = add_locals p.p_body.locals env >>= add_rw (fst p.p_interface.p_shared_vars) >>= add_rw (snd p.p_interface.p_shared_vars) in


    let* init,decls = lower_method (p.p_body.init,()) (env,decls) sm |> E.recover ({info=dummy_pos;stmt=Skip},decls) in
    
    let* (proc_init,_),decls = F.ListM.map (fun ((l,p): loc * _ proc_init) ->
      let open UseMonad(ECSW) in 
      let+ params = F.ListM.map lower_expression p.params in l,{p with params}
    ) p.p_body.proc_init (env,decls) |> ECS.run 
    in 
    let+ loop = 
      let process_cond = function None -> return None | Some c -> let+ (cond,_),_ = lower_expression c (env,decls) |> ECS.run in Some cond in
      let rec aux (l,s) = match s with
      | Statement (s,cond) -> let+ s,_ = lower_method (s,()) (env,decls) sm and* cond = process_cond cond in l,Statement (s,cond)
      | Run (proc,cond) -> let+ cond = process_cond cond in l,Run (proc,cond)
      | PGroup g -> 
        let* cond = process_cond g.cond in
        let+ children = ListM.map aux g.children in
        l,PGroup {g with cond ; children}
      in aux p.p_body.loop
    in
  {p.p_body with init ; proc_init; loop},decls



  let preprocess (sm: ('a,'b) SM.methods_processes SM.t) : ('a,'b) SM.methods_processes SM.t E.t = 
    let module ES = struct 
      module S =  MonadState.M(struct type t = D.t end)
      include Error.MakeTransformer(S)
      let update_env f = S.update f |> lift
      let set_env e = S.set e |> lift
      let get_env = S.get |> lift
    end 
    in
    let open UseMonad(ES) in
    let module TEnv = MakeFromSequencable(SM.DeclEnv.TypeSeq) in
    let module SEnv = MakeFromSequencable(SM.DeclEnv.StructSeq) in
    (* let module MEnv = F.MakeFromSequencable(SM.DeclEnv.MethodSeq) in
    let module PEnv = F.MakeFromSequencable(SM.DeclEnv.ProcessSeq) in *)
    let open SM.DeclEnv in

    (* resolving aliases *)
    let sm = (
    
      let* declEnv = ES.get_env in 

      let* () = 
      TEnv.iter (
        fun (id,({ty; _} as def))  -> 
          let* ty = match ty with 
          | None -> return None 
          | Some t -> 
            let* env = ES.get_env in 
            let* t,env = (follow_type t env) |> ES.S.lift in
            let+ () = ES.set_env env in Some t
          in
          ES.update_env (update_decl id {def with ty} (Self Type))
      ) (get_own_decls declEnv |> get_decls Type) in

      let* env = ES.get_env in 
      
      let* () = SEnv.iter (
        fun (id,(l,{fields; generics}))  -> 
          let* fields = ListM.map (
            fun (name,(l,t,n)) -> 
              let* env = ES.get_env in 
              let* t,env = (follow_type t env) |> ES.S.lift in
              let+ () = ES.set_env env in 
              name,(l,t,n)
          ) fields
          in
          let proto = l,{fields;generics} in 
          ES.update_env (update_decl id proto (Self Struct))
      ) (get_own_decls env |> get_decls Struct)
      in

      let* methods = ListM.map (
        fun ({m_proto;m_body} as m) -> 
          let* rtype = match m_proto.rtype with 
          | None -> return None 
          | Some t -> 
            let* env = ES.get_env in 
            let* t,env = (follow_type t env) |> ES.S.lift in
            let+ () = ES.set_env env in Some t
          in
          let* params = ListM.map (
            fun (({ty;_}:param) as p) -> 
              let* env = ES.get_env in 
              let* ty,env = (follow_type ty env) |> ES.S.lift in
              let+ () = ES.set_env env in {p with ty}
          ) m_proto.params in
          let m = {m with m_proto={m_proto with params; rtype}} in 
          let true_name = (match m_body with Left (sname,_) -> sname | Right _ -> m_proto.name) in
          let+ () = ES.update_env (update_decl m_proto.name ((m_proto.pos,true_name), defn_to_proto (Method m)) (Self Method)) 
          in m
      ) sm.body.methods in

      let* processes = ListM.map (
        fun proc ->
          let* p_params = ListM.map (
            fun (({ty;_}:param) as p) -> 
              let* env = ES.get_env in 
              let* ty,env = (follow_type ty env) |> ES.S.lift in
              let+ () = ES.set_env env in {p with ty}
          ) proc.p_interface.p_params in
        let p = {proc with p_interface={proc.p_interface with p_params}} in
        let+ () = ES.update_env (update_decl p.p_name (p.p_pos, defn_to_proto (Process p)) (Self Process)) 
        in p
      ) sm.body.processes in 

      (* at this point, all types must have an origin *)        


      let* declEnv = ES.get_env in   
      let+ () = SEnv.iter (fun (id,proto) -> check_non_cyclic_struct id proto declEnv |> ES.S.lift) (get_own_decls declEnv |> get_decls Struct) in

      (* Logs.debug (fun m -> m "%s" @@ string_of_declarations declEnv); *)
      {sm with body=SM.{methods; processes}; declEnv}
    ) sm.declEnv |> fst in
    sm
  end
)