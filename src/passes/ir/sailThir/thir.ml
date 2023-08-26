open Common
open TypesCommon
open Logging
open Monad
open IrHir
open AstHir
open SailParser
open ThirUtils
open M
open UseMonad(M)
module SM = SailModule


type expression = ThirUtils.expression
type statement = ThirUtils.statement

module Pass = Pass.MakeFunctionPass(V)(
struct
  let name = "THIR"
  type m_in = HirUtils.statement
  type m_out = statement

  type p_in =  (m_in,HirUtils.expression) AstParser.process_body
  type p_out =  p_in


  let rec lower_lexp (e : Hir.expression) : expression M.t = 
  let rec aux (e:Hir.expression) : expression M.t = 
    let loc = e.info in match e.exp with
    | Variable id -> 
      let* _,t = M.get_var id >>= M.throw_if_none (make_msg loc @@ Printf.sprintf "unknown variable %s" id) in
      let* venv,tenv = M.get_env in 
      let t,tenv = t tenv in 
      let+ () = M.set_env (venv,tenv) in
      buildExp (loc,t) @@ Variable id

    | Deref e -> let* e = lower_rexp e in
      (* return @@ Deref((l,extract_exp_loc_ty e |> snd), e) *)
      begin
        match e.exp with
        | Ref (_,r)  -> return @@ buildExp r.info @@ Deref e
        | _ -> return e
      end
    | ArrayRead (array_exp,idx) -> 
      let* array_exp = aux array_exp and* idx_exp = lower_rexp idx in
      let* array_ty = M.get_type_from_id (array_exp.info) 
      and* idx_ty = M.get_type_from_id (idx_exp.info) in
      begin 
        match array_ty with
        | l,ArrayType (t,sz) -> 
          let* t = M.get_type_id t in 
          let* _ = matchArgParam l idx_ty (dummy_pos,Int 32) |> M.ESC.lift |> M.lift in
          begin 
            (* can do a simple oob check if the type is an int literal *)
            match idx.exp with
            | Literal (LInt n) ->
              M.throw_if (make_msg (fst idx_exp.info) @@ Printf.sprintf "index out of bounds : must be between 0 and %i (got %s)" 
                            (sz - 1) Z.(to_string n.l)
                          )
                  Z.( n.l < ~$0 ||  n.l > ~$sz)   
            | _ -> return ()
          end >>| fun () -> buildExp (loc,t) @@ ArrayRead (array_exp,idx_exp)
        | _ ->  M.throw (make_msg loc "not an array !")
      end
    | StructRead (origin,e,(fl,field)) ->  
      let* e = lower_lexp e in 
      let* ty_e = M.get_type_from_id e.info in
      let+ origin,t = 
        begin
          match ty_e with
          | _,CompoundType {name=l,name;decl_ty=Some S ();_} ->
            let* origin,(_,strct) = find_struct_source (l,name) origin |> M.ESC.lift |> M.lift in
            let*  _,t,_ = List.assoc_opt field strct.fields 
                |> M.throw_if_none (make_msg fl @@ Fmt.str "field '%s' is not part of structure '%s'" field name) 
            in
            let+ t_id = M.get_type_id t in  
            origin,t_id
          | l,t -> 
            let* str = string_of_sailtype_thir (Some (l,t)) |> M.ESC.lift |> M.lift in 
            M.throw (make_msg l @@ Fmt.str "expected a structure but got type '%s'" str)
        end 
      in
      let x : expression = buildExp (loc,t) (StructRead (origin,e,(fl,field))) in
      x

    | _ -> M.throw (make_msg loc "not a lvalue !")

    in aux e
  and lower_rexp (e : Hir.expression) : expression M.t =
  let rec aux (e:Hir.expression) : expression M.t = 
    let loc = e.info in match e.exp with
    | Variable id -> 
      let* _,t = M.get_var id >>= M.throw_if_none (make_msg loc @@ Printf.sprintf "unknown variable %s" id) in
      let* venv,tenv = M.get_env in 
      let t,tenv = t tenv in 
      let+ () = M.set_env (venv,tenv) in
      buildExp (loc,t) @@ Variable id

    | Literal li -> 
      let* () = 
        match li with 
        | LInt t -> 
          let* () = M.throw_if Logging.(make_msg loc "signed integers use a minimum of 2 bits") (t.size < 2) in 
          let max_int = Z.( ~$2 ** t.size - ~$1) in 
          let min_int = Z.( ~-max_int  + ~$1) in
          M.throw_if 
            (
              make_msg loc @@ Fmt.str "type suffix can't contain int literal : i%i is between %s and %s but literal is %s"
              t.size (Z.to_string min_int) (Z.to_string max_int) (Z.to_string t.l)
            ) 
            Z.(lt t.l  min_int || gt t.l max_int) 
        | _ -> return () in
      let+ t = M.get_type_id (sailtype_of_literal li) in 
      buildExp (loc,t) @@ Literal li

    | UnOp (op,e) -> let+ e = aux e in buildExp e.info @@ UnOp (op,e)

    | BinOp (op,le,re) ->
      let* le = aux le in
      let* re = aux re in
      let+ t = check_binop op le.info re.info |> M.recover (snd le.info) in 
      buildExp (loc,t) @@ BinOp (op,le,re)

    | Ref (mut,e) -> 
      let* e = lower_lexp e in 
      let* e_t = M.get_type_from_id e.info in
      let+ t = M.get_type_id (dummy_pos,RefType (e_t,mut)) in
      buildExp (loc,t) @@ Ref(mut, e)

    | ArrayStatic el -> 
      let* first_t = aux (List.hd el) in
      let* first_t = M.get_type_from_id first_t.info in
      let* el = ListM.map (fun e -> 
        let* e = aux e in
        let+ e_t = M.get_type_from_id e.info in
        matchArgParam (fst e.info) e_t first_t |> M.ESC.lift |> M.lift  >>| fun _ -> e
      ) el in 
      let* el = ListM.sequence el in
      let t = dummy_pos,ArrayType (first_t, List.length el) in 
      let+ t_id = M.get_type_id t in 
      buildExp (loc,t_id) (ArrayStatic el)

    | MethodCall (lid,source,args) -> 
      let* (args: expression list) = ListM.map lower_rexp args in 
      let* mod_loc,(_realname,m) = find_function_source e.info None lid source args |> M.ESC.lift |> M.lift in
      let* ret = M.throw_if_none (make_msg e.info "methods in expressions should return a value") m.ret in
      let*  ret_t = M.get_type_id ret in 
      let* x = M.fresh_fvar in
      M.write {info=loc; stmt=DeclVar (false, x, Some ret, None)} >>= fun () ->
      M.write {info=loc; stmt=Invoke {args;id=lid; ret_var = Some x;import=mod_loc}} >>| fun () -> 
      buildExp (loc,ret_t) (Variable x) 

    | ArrayRead _ -> lower_lexp e  (* todo : some checking *)
    | Deref _ -> lower_lexp e  (* todo : some checking *)
    | StructRead _ -> lower_lexp e (* todo : some checking *)
    | StructAlloc (origin,name,fields) -> 
      let* origin,(_l,strct) = find_struct_source name origin |> M.ESC.lift |> M.lift in
      let struct_fields = List.to_seq strct.fields in 

      let fields = FieldMap.(
          merge 
          (
            fun n f1 f2 -> match f1,f2 with 
            | Some _, Some (l,e) -> Some (let+ e = lower_rexp e in n,(l,e))
            | None,None -> None 
            | None, Some (l,_)  -> Some (M.throw @@ make_msg l @@ Fmt.str "no field '%s' in struct '%s'" n (snd name))
            | Some _, None -> Some (M.throw @@ make_msg loc @@ Fmt.str "missing field '%s' from struct '%s'" n (snd name))
          ) 
          (struct_fields |> of_seq) 
          (fields  |> List.to_seq |> of_seq) 
          |> to_seq
        ) in
      
      let* () = M.throw_if (make_msg (fst name) "missing fields ") Seq.(length fields < Seq.length struct_fields) in

      let* fields = SeqM.sequence (Seq.map snd fields) in

      let* () = SeqM.iter2 (fun (_name1,(l,(e:expression))) (_name2,(_,t,_)) ->
        let* e_t = M.get_type_from_id e.info in
        matchArgParam l e_t t |> M.ESC.lift |> M.lift >>| fun _ -> ()
      )
                fields
                struct_fields
      in
      let ty = dummy_pos,CompoundType {origin= Some origin;decl_ty=Some (S ()); name; generic_instances=[]} in 
      let+ ty = M.get_type_id ty in 
      (buildExp (loc,ty) (StructAlloc (origin,name, List.of_seq fields) ))

    | EnumAlloc _ -> M.throw (make_msg loc "todo enum alloc ")
  in aux e


  let lower_method (body,proto : _ * method_sig) (env,tenv:THIREnv.t * _) _ : (m_out * THIREnv.D.t * _) M.E.t = 
    let open UseMonad(M.ESC) in
    let module MF = MonadFunctions(M) in
    let log_and_skip e = M.ESC.log e >>| fun () -> buildStmt e.where Skip in


    let rec aux s : m_out M.ESC.t = 
      let loc = s.info in
      let buildStmt = buildStmt loc in 
      let buildSeq s1 s2 = {info=loc; stmt = Seq (s1, s2)} in 
      let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

      match s.stmt with
      | DeclVar (mut, id, opt_t, (opt_exp : Hir.expression option)) -> 
        let* ((ty,opt_e,s):sailtype * 'b * 'c) =
          begin
            match opt_t,opt_exp with
            | Some t, Some e -> 
              let* e,s = lower_rexp e in
              let* e_t = M.ES.get_type_from_id e.info |> M.ESC.lift in
              matchArgParam (fst e.info) e_t t |> M.ESC.lift >>| fun _ -> t,Some e,s
            | None,Some e -> 
              let* e,s = lower_rexp e in
              let+ e_t = M.ES.get_type_from_id e.info |> M.ESC.lift in
              e_t,Some e,s
            | Some t,None -> return (t,None,buildStmt Skip)
            | None,None -> M.ESC.throw (make_msg loc "can't infere type with no expression")
          end 
        in
        let* ty_id = M.ES.get_type_id ty |> M.ESC.lift in 
        let decl_var = THIREnv.declare_var id (loc,fun e -> ty_id,e) in 
        M.ESC.update_env (fun (st,t) -> M.E.(bind (decl_var st) (fun st -> pure (st,t)))) 
        >>| fun () -> (buildSeqStmt s @@ DeclVar (mut,id,Some ty,opt_e))
        
        
      | Assign(e1, e2) -> 
        let* e1,s1 = lower_lexp e1
        and* e2,s2 = lower_rexp e2 in
        let* e1_t = M.ES.get_type_from_id e1.info |> M.ESC.lift 
        and* e2_t = M.ES.get_type_from_id e2.info |> M.ESC.lift in
        matchArgParam (fst e2.info) e2_t e1_t |> M.ESC.lift >>|
        fun _ -> buildSeq s1 @@ buildSeqStmt s2 @@ Assign(e1, e2)

      | Seq(c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        buildStmt (Seq(c1, c2))


      | If(cond_exp, then_s, else_s) -> 
        let* cond_exp,s = lower_rexp cond_exp in
        let* cond_t = M.ES.get_type_from_id cond_exp.info |> M.ESC.lift in
        let* _ = matchArgParam (fst cond_exp.info) cond_t (dummy_pos,Bool) |> M.ESC.lift in
        let* res = aux then_s in
        begin
        match else_s with
        | None -> return @@ buildSeqStmt s (If(cond_exp, res, None))
        | Some else_ -> let+ else_ = aux else_ in buildSeqStmt s (If(cond_exp, res, Some else_))
        end

      | Loop c -> 
        let+ c = aux c in
        buildStmt (Loop c)

      | Break -> return (buildStmt Break)

      | Case(e, _cases) ->
        let+ e,s = lower_rexp e in
        buildSeqStmt s (Case (e, []))


      | Invoke i -> (* todo: handle var *)
        let* args,s = MF.ListM.map lower_rexp i.args in 
        let* import,_ = find_function_source s.info i.ret_var i.id i.import args |> M.ESC.lift in 
        buildSeqStmt s (Invoke { i with import ; args} ) |> return 

      | Return None as r -> 
        if proto.rtype = None then return (buildStmt r) else 
          log_and_skip (make_msg loc @@ Printf.sprintf "void return but %s returns %s" proto.name (string_of_sailtype proto.rtype))

      | Return (Some e) ->
          let* e,s = lower_rexp e in
          let* t = M.ES.get_type_from_id e.info |> M.ESC.lift in 
          begin
          match proto.rtype with 
          | None -> 
            log_and_skip (make_msg loc @@ Printf.sprintf "returns %s but %s doesn't return anything"  (string_of_sailtype (Some t)) proto.name)
          | Some r ->
            matchArgParam (fst e.info) t r |> M.ESC.lift >>| fun _ ->
            buildSeqStmt s (Return (Some e))
          end

      | Block c ->
          let* () = M.ESC.update_env (fun (e,t) -> (THIREnv.new_frame e,t) |> M.E.pure) in
          let* res = aux c in 
          let+ () =  M.ESC.update_env (fun (e,t) -> (THIREnv.pop_frame e,t) |> M.E.pure) in
          buildStmt (Block res)

      | Skip -> return (buildStmt Skip)

    in 
    M.(E.bind (ESC.run aux body (env,tenv)) (fun (x,y) -> E.pure (x,snd env,y))) |> Logger.recover (buildStmt dummy_pos Skip,snd env,tenv)

  let preprocess = resolve_types  (* todo : create semantic types + type inference *)

  let lower_process (c:p_in process_defn) (env,tenv) _ = M.E.pure (c.p_body,snd env,tenv)

  end
)
