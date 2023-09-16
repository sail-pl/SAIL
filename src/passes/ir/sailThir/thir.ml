open Common
open TypesCommon
open Logging
open Monad
open IrHir
open SailParser
open IrAst
open ThirUtils
open M
open UseMonad(M)
module SM = SailModule

module Pass = Pass.MakeFunctionPass(V)(
struct
  let name = "THIR"
  type m_in = HirUtils.statement
  type m_out = ThirUtils.statement

  type p_in =  (m_in,HirUtils.expression) AstParser.process_body
  type p_out =  p_in



  let rec lower_lexp (exp : HirUtils.expression) : expression M.t = 
  let rec aux (exp:HirUtils.expression) : expression M.t = 

    match exp.node with
    | Variable id -> 
      let* _,t = M.get_var id >>= M.throw_if_none (make_msg exp.tag @@ Printf.sprintf "unknown variable %s" id) in
      let* venv,tenv = M.get_env in 
      let t,tenv = t tenv in 
      let+ () = M.set_env (venv,tenv) in
      buildExp exp.tag t @@ Variable id

    | Deref e -> let* e = lower_rexp e in
      (* return @@ Deref((l,extract_exp_loc_ty e |> snd), e) *)
      begin
        match e.node with
        | Ref (_,r)  -> return @@ buildExp r.tag.loc r.tag.ty @@ Deref e
        | _ -> return e
      end

    | ArrayRead ar -> 
      let* array = aux ar.array and* idx = lower_rexp ar.idx in
      let* array_ty = M.get_type_from_id (mk_locatable array.tag.loc array.tag.ty) and* idx_ty = M.get_type_from_id (mk_locatable idx.tag.loc idx.tag.ty) in
      begin 
        match array_ty.value with
        | ArrayType (t,sz) -> 
          let* t = M.get_type_id t in 
          let* _ = matchArgParam array_ty.loc idx_ty (mk_locatable dummy_pos @@ Int 32) |> M.ESC.lift |> M.lift in
          begin 
            (* can do a simple oob check if the type is an int literal *)
            match idx.node with
            | Literal (LInt n) ->
              M.throw_if (make_msg idx.tag.loc @@ Printf.sprintf "index out of bounds : must be between 0 and %i (got %s)" 
                            (sz - 1) Z.(to_string n.l)
                          )
                  Z.( n.l < ~$0 ||  n.l > ~$sz)   
            | _ -> return ()
          end >>| fun () -> buildExp exp.tag t @@ ArrayRead {array;idx}
        | _ ->  M.throw (make_msg exp.tag "not an array !")
      end
      
    | StructRead s ->  
      let* strct = lower_lexp s.value.strct in 
      let* ty = M.get_type_from_id (mk_locatable strct.tag.loc strct.tag.ty) in
      let+ import,t = 
        begin
          match ty.value with
          | CompoundType {name;decl_ty=Some S ();_} ->
            let* origin,(_,strct) = find_struct_source name s.import |> M.ESC.lift |> M.lift in
            let*  f = List.assoc_opt s.value.field.value strct.fields 
                |> M.throw_if_none (make_msg s.value.field.loc @@ Fmt.str "field '%s' is not part of structure '%s'" s.value.field.value name.value) 
            in
            let+ t_id = M.get_type_id (fst f.value) in  
            origin,t_id
          | t -> 
            let* str = string_of_sailtype_thir (Some (mk_locatable ty.loc t)) |> M.ESC.lift |> M.lift in 
            M.throw (make_msg ty.loc @@ Fmt.str "expected a structure but got type '%s'" str)
        end 
      in
      buildExp ty.loc t @@ StructRead2 (mk_importable import Ast.{field=s.value.field;strct})
    
    | BinOp _ | Literal _ | UnOp _ |  Ref _  | ArrayStatic _ | StructAlloc _ | EnumAlloc _ | MethodCall _ -> 
      M.throw (make_msg exp.tag "not a lvalue !")

    in aux exp
  and lower_rexp (exp : HirUtils.expression) : expression M.t =
  let rec aux (exp: HirUtils.expression) : expression M.t = 
    match exp.node with
    | Variable id -> 
      let* _,t = M.get_var id >>= M.throw_if_none (make_msg exp.tag @@ Printf.sprintf "unknown variable %s" id) in
      let* venv,tenv = M.get_env in 
      let t,tenv = t tenv in 
      let+ () = M.set_env (venv,tenv) in
      buildExp exp.tag t @@ Variable id

    | Literal li -> 
      let* () = 
        match li with 
        | LInt t -> 
          let* () = M.throw_if Logging.(make_msg exp.tag "signed integers use a minimum of 2 bits") (t.size < 2) in 
          let max_int = Z.( ~$2 ** t.size - ~$1) in 
          let min_int = Z.( ~-max_int  + ~$1) in
          M.throw_if 
            (
              make_msg exp.tag @@ Fmt.str "type suffix can't contain int literal : i%i is between %s and %s but literal is %s"
              t.size (Z.to_string min_int) (Z.to_string max_int) (Z.to_string t.l)
            ) 
            Z.(lt t.l  min_int || gt t.l max_int) 
        | _ -> return () in
      let+ t = M.get_type_id (sailtype_of_literal li) in 
      buildExp exp.tag t @@ Literal li

    | UnOp (op,e) -> let+ e = aux e in buildExp exp.tag e.tag.ty @@ UnOp (op,e)

    | BinOp bop ->
      let* left = aux bop.left in
      let* right = aux bop.right in
      let+ t = check_binop bop.op (mk_locatable left.tag.loc left.tag.ty) (mk_locatable right.tag.loc right.tag.ty) |> M.recover left.tag.ty in 
      buildExp exp.tag t @@ BinOp {op=bop.op;left;right}

    | Ref (mut,e) -> 
      let* e = lower_lexp e in 
      let* e_t = M.get_type_from_id (mk_locatable e.tag.loc e.tag.ty) in
      let+ t = M.get_type_id (mk_locatable dummy_pos @@ RefType (e_t,mut)) in
      buildExp exp.tag t @@ Ref(mut, e)

    | ArrayStatic el -> 
      let* first_t = aux (List.hd el) in
      let* first_t = M.get_type_from_id (mk_locatable first_t.tag.loc first_t.tag.ty) in
      let* el = ListM.map (fun e -> 
        let* e = aux e in
        let+ e_t = M.get_type_from_id (mk_locatable e.tag.loc e.tag.ty) in
        matchArgParam e.tag.loc e_t first_t |> M.ESC.lift |> M.lift  >>| fun _ -> e
      ) el in 
      let* el = ListM.sequence el in
      let t = exp.tag,ArrayType (first_t, List.length el) in 
      let+ t_id = M.get_type_id (mk_locatable (fst t) (snd t)) in 
      buildExp exp.tag t_id (ArrayStatic el)

    | MethodCall mc -> 
      let* args = ListM.map lower_rexp mc.value.args in 
      let* import,(_realname,m) = find_function_source exp.tag None mc.value.id mc.import args |> M.ESC.lift |> M.lift in
      let* ty = M.throw_if_none (make_msg exp.tag "methods in expressions should return a value") m.ret  in
      let* ty_t = M.get_type_id ty in 
      let* ret_var = M.fresh_fvar in
      M.write {tag={loc=exp.tag;ty=""}; node=DeclVar2 {mut=false;id=ret_var;ty}} >>= fun () ->
      let x = Ast.{args;id=mc.value.id; ret_var = Some ret_var} in 
      M.write {tag={loc=exp.tag;ty=""}; node=Invoke2 (mk_importable import x)} >>| fun () -> 
      buildExp exp.tag ty_t (Variable ret_var) 

    | ArrayRead _
    | Deref _
    | StructRead _  -> lower_lexp exp (* todo : some checking *)

    | StructAlloc s -> 
      let* import,(_l,strct) = find_struct_source s.value.name s.import |> M.ESC.lift |> M.lift in
      let struct_fields = List.to_seq strct.fields in 

      let fields = FieldMap.(
          merge 
          (
            fun n f1 f2 -> match f1,f2 with 
            | Some _, Some e -> Some (let+ e = lower_rexp e.value in n,e)
            | None,None -> None 
            | None, Some l  -> Some (M.throw @@ make_msg l.loc @@ Fmt.str "no field '%s' in struct '%s'" n s.value.name.value)
            | Some _, None -> Some (M.throw @@ make_msg s.value.name.loc @@ Fmt.str "missing field '%s' from struct '%s'" n s.value.name.value)
          ) 
          (struct_fields |> of_seq) 
          (s.value.fields |> List.to_seq  |> of_seq) 
          |> to_seq
        ) in
      
      let* () = M.throw_if (make_msg s.value.name.loc "missing fields ") Seq.(length fields < Seq.length struct_fields) in

      let* fields: (string * expression) Seq.t = SeqM.sequence (Seq.map snd fields) in

      let* () = 
        SeqM.iter2 (fun (_name1,e) (_name2,t) ->
        let* e_t = M.get_type_from_id (mk_locatable e.tag.loc e.tag.ty) in
        matchArgParam e.tag.loc e_t (fst t.value) |> M.ESC.lift |> M.lift >>| fun _ -> ()
        )
        fields
        struct_fields
      in
      let _fields = List.of_seq fields in 
      let l,ty = dummy_pos,CompoundType {origin= Some import;decl_ty=Some (S ()); name=s.value.name; generic_instances=[]} in 
      let+ ty = M.get_type_id (mk_locatable l ty) in 
      buildExp exp.tag ty @@ StructAlloc2 (mk_importable import Ast.{name=s.value.name;fields=[] (* FIXMEEEEEEEEEEEEE *)} )

    | EnumAlloc _ -> M.throw (make_msg exp.tag "todo enum alloc ")
  in aux exp


  let lower_method (body,proto : _ * method_sig) (env,tenv:THIREnv.t * _) _ : (m_out * THIREnv.D.t * _) M.E.t = 
    let open UseMonad(M.ESC) in
    let module MF = MonadFunctions(M) in
    let log_and_skip e = M.ESC.log e >>| fun () -> Ast.buildStmt {loc=e.where;ty="unit"} Skip in


    let rec aux (s: m_in) : m_out M.ESC.t = 
      let loc = s.tag in
      let buildStmt = Ast.buildStmt {loc;ty="unit"} in 
      let buildSeq = Ast.buildSeq {loc;ty="unit"} in 
      let buildSeqStmt s1 s2 = buildSeq s1 @@ buildStmt s2 in

      match s.node with
      | DeclVar d -> 
        let* ty,opt_e,s =
          begin
            match d.ty,d.value with
            | Some t, Some e -> 
              let* e,s = lower_rexp e in
              let* e_t = M.ES.get_type_from_id (mk_locatable e.tag.loc e.tag.ty) |> M.ESC.lift in
              matchArgParam e.tag.loc e_t t |> M.ESC.lift >>| fun _ -> t,Some e,s
            | None,Some e -> 
              let* e,s = lower_rexp e in
              let+ e_t = M.ES.get_type_from_id (mk_locatable e.tag.loc e.tag.ty) |> M.ESC.lift in
              e_t,Some e,s
            | Some t,None -> return (t,None,buildStmt Skip)
            | None,None -> M.ESC.throw (make_msg loc "can't infere type with no expression")
          end 
        in
        let* ty_id = M.ES.get_type_id ty |> M.ESC.lift in 
        let decl_var = THIREnv.declare_var d.id (loc,fun e -> ty_id,e) in 
        M.ESC.update_env (fun (st,t) -> M.E.(bind (decl_var st) (fun st -> pure (st,t)))) >>| fun () -> 
        let s1 = buildSeqStmt s @@ DeclVar2 {mut=d.mut;ty;id=d.id;} in
        let s2 = match opt_e with None -> Ast.Skip | Some value -> Assign {path=buildExp loc ty_id (Variable d.id); value} in
        buildSeqStmt s1 s2
        
        
      | Assign a -> 
        let* value,s1 = lower_rexp a.value
        and* path,s2 = lower_lexp a.path in
        let* value_t = M.ES.get_type_from_id (mk_locatable value.tag.loc value.tag.ty) |> M.ESC.lift 
        and* path_t = M.ES.get_type_from_id  (mk_locatable path.tag.loc path.tag.ty) |> M.ESC.lift in
        matchArgParam path.tag.loc path_t value_t |> M.ESC.lift >>|
        fun _ -> buildSeq s1 @@ buildSeqStmt s2 @@ Assign {path;value}

      | Seq (c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        buildStmt (Seq (c1, c2))


      | If if_ -> 
        let* cond,s = lower_rexp if_.cond in
        let* cond_t = M.ES.get_type_from_id (mk_locatable cond.tag.loc cond.tag.ty) |> M.ESC.lift in
        let* _ = matchArgParam cond.tag.loc cond_t (mk_locatable dummy_pos Bool) |> M.ESC.lift in
        let* then_ = aux if_.then_ in
        begin
        match if_.else_ with
        | None -> return @@ buildSeqStmt s (If {cond;then_;else_=None})
        | Some else_ -> let+ else_ = aux else_ in buildSeqStmt s (If {cond;then_;else_=Some else_})
        end

      | Loop c -> 
        let+ c = aux c in
        buildStmt (Loop c)

      | Break -> return (buildStmt Break)

      | Case c ->
        let+ switch,s = lower_rexp c.switch in
        buildSeqStmt s (Case {switch;cases=[]})


      | Invoke i -> (* todo: handle var *)
        let* args,s = MF.ListM.map lower_rexp i.value.args in 
        let* import,_ = find_function_source s.tag.loc i.value.ret_var i.value.id i.import args |> M.ESC.lift in 
        buildSeqStmt s (Invoke2 (mk_importable import Ast.{args;ret_var=i.value.ret_var;id=i.value.id} )) |> return 

      | Return None -> 
        if proto.rtype = None then return (buildStmt (Return None)) else 
          log_and_skip (make_msg loc @@ Printf.sprintf "void return but %s returns %s" proto.name (string_of_sailtype proto.rtype))

      | Return (Some e) ->
          let* e,s = lower_rexp e in
          let* t = M.ES.get_type_from_id (mk_locatable e.tag.loc e.tag.ty) |> M.ESC.lift in 
          begin
          match proto.rtype with 
          | None -> 
            log_and_skip (make_msg loc @@ Printf.sprintf "returns %s but %s doesn't return anything"  (string_of_sailtype (Some t)) proto.name)
          | Some r ->
            matchArgParam e.tag.loc t r |> M.ESC.lift >>| fun _ ->
            buildSeqStmt s (Return (Some e))
          end

      | Block c ->
          let* () = M.ESC.update_env (fun (e,t) -> (THIREnv.new_frame e,t) |> M.E.pure) in
          let* res = aux c in 
          let+ () =  M.ESC.update_env (fun (e,t) -> (THIREnv.pop_frame e,t) |> M.E.pure) in
          buildStmt (Block res)

      | Skip -> return (buildStmt Skip)

    in 
    M.(E.bind (ESC.run aux body (env,tenv)) (fun (x,y) -> E.pure (x,snd env,y))) |> Logger.recover (Ast.buildStmt {loc=dummy_pos; ty="unit"} Skip,snd env,tenv)

  let preprocess = resolve_types  (* todo : create semantic types + type inference *)

  let lower_process (c:p_in process_defn) (env,tenv) _ = M.E.pure (c.p_body,snd env,tenv)

  end
)
