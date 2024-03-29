open Common
open TypesCommon
open Error
open Monad
open IrHir
open AstHir
open SailParser
open ThirMonad
open ThirUtils

open MonadSyntax(ES)
open MonadFunctions(ES)
open MonadOperator(ES)


type expression = ThirUtils.expression
type statement = ThirUtils.statement

module Pass = Pass.MakeFunctionPass(V)(
struct
  let name = "THIR"
  type m_in = HirUtils.statement
  type m_out = statement

  type p_in =  (m_in,HirUtils.expression) AstParser.process_body
  type p_out =  p_in


  let rec lower_lexp (e : Hir.expression) : expression ES.t = 
  let rec aux (e:Hir.expression) : expression ES.t = 
    let loc = e.info in  match e.exp with
    | Variable id -> 
      let+ (_,(_,t)) = ES.get_var id >>= ES.throw_if_none (Error.make loc @@ Printf.sprintf "unknown variable %s" id) in
      buildExp (loc,t) @@ Variable id

    | Deref e -> let* e = lower_rexp e in
      (* return @@ Deref((l,extract_exp_loc_ty e |> snd), e) *)
      begin
        match e.exp with
        | Ref (_,r)  -> return @@ buildExp r.info @@ Deref e
        | _ -> return e
      end
    | ArrayRead (array_exp,idx) -> let* array_exp = aux array_exp and* idx = lower_rexp idx in
      begin 
        match snd array_exp.info with
        | ArrayType (t,sz) -> 
          let* _ = matchArgParam (idx.info) (Int 32) in
          begin 
            (* can do a simple oob check if the type is an int literal *)
            match idx.exp with
            | Literal (LInt n) ->
              ES.throw_if (Error.make (fst idx.info) @@ Printf.sprintf "index out of bounds : must be between 0 and %i (got %s)" 
                            (sz - 1) Z.(to_string n.l)
                          )
                  Z.( n.l < ~$0 ||  n.l > ~$sz)   
            | _ -> return ()
          end >>| fun () -> buildExp (loc,t) @@ ArrayRead (array_exp,idx)
        | _ ->  ES.throw (Error.make loc "not an array !")
      end
    | StructRead (origin,e,(fl,field)) ->  
      let* e = lower_lexp e in 
      let+ origin,t = 
      begin
        match e.info with
        | _, CompoundType {name=l,name;decl_ty=Some S ();_} ->
          let* origin,(_,strct) = find_struct_source (l,name) origin in
          let+  _,t,_ = List.assoc_opt field strct.fields 
              |> ES.throw_if_none (Error.make fl @@ Fmt.str "field '%s' is not part of structure '%s'" field name) 
          in origin,t
        | l,t -> 
          let* str = string_of_sailtype_thir (Some t) in 
          ES.throw (Error.make l @@ Fmt.str "expected a structure but got type '%s'" str)
      end 
      in
      let x : expression = buildExp (loc,t) (StructRead (origin,e,(fl,field))) in
      x

    | _ -> ES.throw (Error.make loc "not a lvalue !")

    in aux e
  and lower_rexp (e : Hir.expression) : expression ES.t =
  let rec aux (e:Hir.expression) : expression ES.t = 
    let loc = e.info in match e.exp with
    | Variable id -> 
      let+ (_,(_,t)) = ES.get_var id >>= ES.throw_if_none (Error.make loc @@ Printf.sprintf "unknown variable %s" id) in
      buildExp (loc,t) @@ Variable id
    | Literal li -> 
      let+ () = 
        match li with 
        | LInt t -> 
          let* () = ES.throw_if Error.(make loc "signed integers use a minimum of 2 bits") (t.size < 2) in 
          let max_int = Z.( ~$2 ** t.size - ~$1) in 
          let min_int = Z.( ~-max_int  + ~$1) in
          ES.throw_if 
            (
              Error.make loc @@ Fmt.str "type suffix can't contain int literal : i%i is between %s and %s but literal is %s"
              t.size (Z.to_string min_int) (Z.to_string max_int) (Z.to_string t.l)
            ) 
            Z.(lt t.l  min_int || gt t.l max_int) 
        | _ -> return () in
      let t = sailtype_of_literal li in 
      buildExp (loc,t) @@ Literal li
    | UnOp (op,e) -> let+ e = aux e in buildExp e.info @@ UnOp (op,e)
    | BinOp (op,le,re) ->
      let* le = aux le in
      let* re = aux re in
      let lt = le.info  and rt = re.info in
      let+ t = check_binop op lt rt |> ES.recover (snd lt) in 
      buildExp (loc,t) @@ BinOp (op,le,re)

    | Ref (mut,e) -> let+ e = lower_lexp e in 
      let t = RefType (snd e.info,mut) in
      buildExp (loc,t) @@ Ref(mut, e)
    | ArrayStatic el -> 
      let* first_t = aux (List.hd el) in
      let first_t = snd first_t.info in
      let* el = ListM.map (
        fun e -> let+ e = aux e in
        matchArgParam e.info first_t  >>| fun _ -> e
      ) el in 
      let+ el = ListM.sequence el in
      let t = ArrayType (first_t, List.length el) in 
      buildExp (loc,t) (ArrayStatic el)

    | MethodCall ((l,name) as lid,source,el) -> 
      let* (el: expression list) = ListM.map lower_rexp el in 
      let* mod_loc,(_realname,m) = find_function_source e.info None lid source el in
      let+ ret = ES.throw_if_none (Error.make e.info "methods in expressions should return a value") m.ret in
      buildExp (loc,ret) (MethodCall ((l,name),mod_loc,el)) 


    | ArrayRead _ -> lower_lexp e  (* todo : some checking *)
    | Deref _ -> lower_lexp e  (* todo : some checking *)
    | StructRead _ -> lower_lexp e (* todo : some checking *)
    | StructAlloc (origin,name,fields) -> 
      let* origin,(_l,strct) = find_struct_source name origin in
      let struct_fields = List.to_seq strct.fields in 

      let fields = FieldMap.(merge (
        fun n f1 f2 -> match f1,f2 with 
        | Some _, Some e -> Some(let+ e = lower_rexp e in (n,e))
        | None,None -> None 
        | None, Some (e:Hir.expression)  -> Some (ES.throw @@ Error.make e.info @@ Fmt.str "no field '%s' in struct '%s'" n (snd name))
        | Some _, None -> Some (ES.throw @@ Error.make loc @@ Fmt.str "missing field '%s' from struct '%s'" n (snd name))
      ) (struct_fields |> of_seq) (fields |> List.to_seq |> of_seq ) |> to_seq) in
      
      let* () = ES.throw_if (Error.make (fst name) "missing fields ") Seq.(length fields < Seq.length struct_fields) in

      let* fields = SeqM.sequence (Seq.map snd fields) in

      let+ () = SeqM.iter2 (fun (_name1,(e:expression)) (_name2,(_,t,_)) -> matchArgParam e.info t >>| fun _ -> ())
      fields
      struct_fields
      in
      let ty = CompoundType {origin= Some origin;decl_ty=Some (S ()); name; generic_instances=[]} in 
      (buildExp (loc,ty) (StructAlloc (origin,name, List.of_seq fields)))

    | EnumAlloc _ -> ES.throw (Error.make loc "todo enum alloc ")
  in aux e


  let lower_method (body,proto : _ * method_sig) (env:THIREnv.t) _ : (m_out * THIREnv.D.t) E.t = 
    let log_and_skip e = ES.log e >>| fun () -> buildStmt e.where Skip
    in 

    let rec aux s : m_out ES.t = 
      let loc = s.info in
      let buildStmt = buildStmt loc in 
      match s.stmt with
      | DeclVar (mut, id, opt_t, (opt_exp : Hir.expression option)) -> 
        let* ((ty,opt_e):sailtype * 'b) =
          begin
            match opt_t,opt_exp with
            | Some t, Some e -> 
              let* e = lower_rexp e in
              matchArgParam e.info t >>| fun _ -> t,Some e
            | None,Some e -> 
              let+ e = lower_rexp e in
              (snd e.info),Some e
            | Some t,None -> return (t,None)
            | None,None -> ES.throw (Error.make loc "can't infere type with no expression")
          end 
        in
        ES.update (fun st -> THIREnv.declare_var id (loc,(mut,ty)) st) 
        >>| fun () -> (buildStmt @@ DeclVar (mut,id,Some ty,opt_e))
        
        
      | Assign(e1, e2) -> 
        let* e1 = lower_lexp e1
        and* e2 = lower_rexp e2 in
        matchArgParam e2.info (snd e1.info) >>|
        fun _ -> buildStmt (Assign(e1, e2))

      | Seq(c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        buildStmt (Seq(c1, c2))


      | If(cond_exp, then_s, else_s) -> 
        let* cond_exp = lower_rexp cond_exp in
        let* _ = matchArgParam cond_exp.info Bool  in
        let* res = aux then_s in
        begin
        match else_s with
        | None -> return @@ buildStmt (If(cond_exp, res, None))
        | Some s -> let+ s = aux s in buildStmt (If(cond_exp, res, Some s))
        end

      | Loop c -> 
        let+ c = aux c in
        buildStmt (Loop c)

      | Break -> return (buildStmt Break)

      | Case(e, _cases) ->
        let+ e = lower_rexp e in
        buildStmt (Case (e, []))


      | Invoke (var, mod_loc, id, el) -> (* todo: handle var *)
        let* el = ListM.map lower_rexp el in 
        let* origin,_ = find_function_source s.info var id mod_loc el in 
        buildStmt (Invoke(var,origin, id,el)) |> return 

      | Return None as r -> 
        if proto.rtype = None then return (buildStmt r) else 
          log_and_skip (Error.make loc @@ Printf.sprintf "void return but %s returns %s" proto.name (string_of_sailtype proto.rtype))

      | Return (Some e) ->
          let* e = lower_rexp e in
          let _,t as lt = e.info in 
          begin
          match proto.rtype with 
          | None -> 
            log_and_skip (Error.make loc @@ Printf.sprintf "returns %s but %s doesn't return anything"  (string_of_sailtype (Some t)) proto.name)
          | Some r ->
            matchArgParam lt r >>| fun _ ->
            buildStmt (Return (Some e))
          end

      | Block c ->
          let* () = ES.update (fun e -> THIREnv.new_frame e |> E.pure) in
          let* res = aux c in 
          let+ () =  ES.update (fun e -> THIREnv.pop_frame e |> E.pure) in
          buildStmt (Block res)

      | Skip -> return (buildStmt Skip)

    in 
    ES.run (aux body env) |> Logger.recover (buildStmt dummy_pos Skip,snd env)

    let preprocess = Logger.pure

    let lower_process (c:p_in process_defn) env _ = E.pure (c.p_body,snd env)

  end
)
