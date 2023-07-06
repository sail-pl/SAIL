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

  type in_body = AstParser.statement
  type out_body = statement
      
  open MonadFunctions(ECSW)
  open MonadOperator(ECSW)
  open MakeOrderedFunctions(String)

  let get_hint id env = 
    MonadOption.M.bind (List.nth_opt (HIREnv.get_closest id env) 0) (fun id -> Some (None,Printf.sprintf "Did you mean %s ?" id))


  let lower_expression (e : AstParser.expression) : expression ECSW.t = 
    let open MonadSyntax(ECSW) in
    let rec aux (info,e : AstParser.expression) : expression ECSW.t  = 
    match e with 
      | Variable id -> return {info; exp=Variable id}
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

  let lower_function (c:in_body Pass.function_type) (env:HIREnv.t) _ : (out_body * HIREnv.D.t) E.t = 
  let open MonadSyntax(ECS) in
  let open MonadOperator(ECS) in 
    
  let rec aux (info,s : in_body) : out_body ECS.t = 
  
    let buildSeq s1 s2 = {info; stmt = Seq (s1, s2)} in 
    let buildStmt stmt = {info;stmt} in
    let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

    match s with
    | DeclVar (mut, id, t, e ) -> 
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
    | Block c -> let+ c = aux c in buildStmt (Block c)
    
    | Run (l_id,id as lid, el) -> 
      let* () = ECS.log_if (Error.make l_id "a process cannot call itself (yet)") (id = c.name) in
      let* m = ECS.get_decl id (Self Process) and* env = ECS.get in
      let* () = ECS.log_if (let hint = get_hint id env in (Error.make l_id "unknown process" ~hint)) (m = None) in
      let* () = ECS.log_if (Error.make l_id "this is a process but methods cannot call processes") (c.bt = BMethod) in
      let+ el,s = ListM.map lower_expression el in 
      buildSeqStmt s (Run(lid, el))

    | _ when c.bt = Pass.BMethod -> 
      let+ () = ECS.log (Error.make info @@ Printf.sprintf "method %s : methods can't contain reactive statements" c.name) 
      in buildStmt Skip 

    | DeclSignal s -> return @@ buildStmt (DeclSignal s)
    | Emit s -> return @@ buildStmt (Emit s)
    | Await s -> return @@ buildStmt @@ When (s, buildStmt Skip)
    | When (s, c) -> let+ c = aux c in buildStmt (When (s, c))
    | Watching (s, c) ->  let+ c = aux c in buildStmt (Watching (s, c))
    | Par (c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in buildStmt (Par(c1,c2))

    in
    ECS.run (aux c.body env) |> E.recover ({info=dummy_pos;stmt=Skip},snd env)

    let preprocess (sm: 'a SM.t) : 'a SM.t E.t = 
      let module ES = struct 
        module S =  MonadState.M(struct type t = D.t end)
        include Error.MakeTransformer(S)
        let update_env f = S.update f |> lift
        let set_env e = S.set e |> lift
        let get_env = S.get |> lift
      end 
      in
      let open MonadSyntax(ES) in
      let open MonadOperator(ES) in
      let module F = MonadFunctions(ES) in
      let module TEnv = F.MakeFromSequencable(SM.DeclEnv.TypeSeq) in
      let module SEnv = F.MakeFromSequencable(SM.DeclEnv.StructSeq) in
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
            let* fields = F.ListM.map (
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

        let* methods = F.ListM.map (
          fun ({m_proto;m_body} as m) -> 
            let* rtype = match m_proto.rtype with 
            | None -> return None 
            | Some t -> 
              let* env = ES.get_env in 
              let* t,env = (follow_type t env) |> ES.S.lift in
              let+ () = ES.set_env env in Some t
            in
            let* params = F.ListM.map (
              fun (({ty;_}:param) as p) -> 
                let* env = ES.get_env in 
                let* ty,env = (follow_type ty env) |> ES.S.lift in
                let+ () = ES.set_env env in {p with ty}
            ) m_proto.params in
            let m = {m with m_proto={m_proto with params; rtype}} in 
            let true_name = (match m_body with Left (sname,_) -> sname | Right _ -> m_proto.name) in
            let+ () = ES.update_env (update_decl m_proto.name ((m_proto.pos,true_name), defn_to_proto (Method m)) (Self Method)) 
            in m
        ) sm.methods in

        let* processes = F.ListM.map (
          fun ({p_interface=p,s;p_name;p_pos;_} as pr)  ->
            let* p = F.ListM.map (
              fun (({ty;_}:param) as p) -> 
                let* env = ES.get_env in 
                let* ty,env = (follow_type ty env) |> ES.S.lift in
                let+ () = ES.set_env env in {p with ty}
            ) p in
          let p = {pr with p_interface=p,s} in
          let+ () = ES.update_env (update_decl p_name (p_pos, defn_to_proto (Process p)) (Self Process)) 
          in p
        ) sm.processes in 

        (* at this point, all types must have an origin *)        


        let* declEnv = ES.get_env in   
        let+ () = SEnv.iter (fun (id,proto) -> check_non_cyclic_struct id proto declEnv |> ES.S.lift) (get_own_decls declEnv |> get_decls Struct) in

        (* Logs.debug (fun m -> m "%s" @@ string_of_declarations declEnv); *)
        {sm with methods; processes; declEnv}
      ) sm.declEnv |> fst in
      sm
  end
)