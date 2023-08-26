open Common
open TypesCommon
open Monad
open SailParser

type expression = (loc,l_str option) AstHir.expression
type statement = (loc,l_str option,expression) AstHir.statement

module M = HirMonad.Make( struct
  type t = statement
  let mempty : t = {info=dummy_pos; stmt=Skip}
  let mconcat : t -> t -> t = fun x y -> {info=dummy_pos; stmt=Seq (x,y)}
  end
)

open M
module D = SailModule.DeclEnv

let lower_expression (e : AstParser.expression) : expression M.t = 
  let open UseMonad(M) in
  let rec aux (info,e : AstParser.expression) : expression M.t  = 
  let open AstHir in 
  match e with 
  | Variable id -> 
    let* v = (M.ECS.find_var id |> M.lift) in
    M.throw_if_none Logging.(make_msg info @@ Fmt.str "undeclared variable '%s'" id)  v >>| fun _ ->
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
    let* () = M.throw_if Logging.(make_msg info "duplicate fields") List.(length m <> length m') in
    let+ m' = ListM.map (aux |> pairMap2 |> pairMap2) m' in
    {info; exp=StructAlloc (origin, id, m')}

  | EnumAlloc (id, el) ->
    let+ el = ListM.map aux el in  {info;exp=EnumAlloc (id, el)}

    
  | MethodCall (import, id, el) -> let+ el = ListM.map aux el in {info ; exp=MethodCall(id, import, el)}    
  in aux e


open UseMonad(M.E)

let find_symbol_source ?(filt = [E (); S (); T ()] ) (loc,id: l_str) (import : l_str option) (env : D.t) : (l_str * D.decls)  M.E.t =
  match import with
  | Some (iloc,name) -> 
    if name = Constants.sail_module_self || name = D.get_name env then 
        let+ decl = 
          D.find_decl id (Self (Filter filt)) env 
          |> M.E.throw_if_none Logging.(make_msg loc @@ "no declaration named '" ^ id ^ "' in current module ")
        in
        (iloc,D.get_name env),decl
    else
      let+ t = 
        M.E.throw_if_none Logging.(make_msg iloc  ~hint:(Some (None,Fmt.str "try importing the module with 'import %s'" name)) @@ "unknown module " ^ name)  
                        (List.find_opt (fun {mname;_} -> mname = name) (D.get_imports env)) >>= fun _ ->
        M.E.throw_if_none Logging.(make_msg loc @@ "declaration "  ^ id ^ " not found in module " ^ name)
                        (D.find_decl id (Specific (name, Filter filt)) env)
      in
      (iloc,name),t
  | None -> (* find it ourselves *)
    begin
      let decl = D.find_decl id (All (Filter filt)) env in
      match decl with
      | [i,m] -> 
        (* Logs.debug (fun m -> m "'%s' is from %s" id i.mname); *)
        return ((dummy_pos,i.mname),m)

      | [] ->  M.E.throw Logging.(make_msg loc @@ "unknown declaration " ^ id)

      | _ as choice -> M.E.throw 
                    @@ Logging.make_msg loc ~hint:(Some (None,"specify one with '::' annotation")) 
                    @@ Fmt.str "multiple definitions for declaration %s : \n\t%s" id 
                      (List.map (fun (i,def) -> match def with T def -> Fmt.str "from %s : %s" i.mname (string_of_sailtype (def.ty)) | _ -> "") choice |> String.concat "\n\t")
  end

let follow_type ty env : (sailtype * D.t) M.E.t = 
  let current = SailModule.DeclEnv.get_name env in

  (* Logs.debug (fun m -> m "following type '%s'" (string_of_sailtype (Some ty))); *)

  let rec aux (l_ty,ty') path : (sailtype * ty_defn list) M.E.t = 
    (* Logs.debug (fun m -> m "path: %s" (List.map (fun ({name;_}:ty_defn) -> name)path |> String.concat " ")); *)
    let+ (t,path : sailtype_ * ty_defn list) = 
      match ty' with 
      
      | ArrayType (t,n) -> let+ t,path = aux t path in  ArrayType (t,n),path
      | Box t -> let+ t,path = aux t path in Box t,path
      | RefType (t,mut) -> let+ t,path = aux t path in RefType (t,mut),path
      | Bool | Char | Int _ | Float | String | GenericType _ as t ->  (* basic type, stop *)
        (* Logs.debug (fun m -> m "'%s' resolves to '%s'" (string_of_sailtype (Some ty)) (string_of_sailtype (Some ty'))); *)
        return (t,path)
      | CompoundType {origin;name=id;generic_instances;_} -> (* compound type, find location and definition *) 
      let* (l,origin),def = find_symbol_source id origin env in 
      let default = fun ty -> CompoundType {origin=Some (l,origin);name=id; generic_instances;decl_ty=Some ty} in 
      begin
        match def with
        | T def when origin=current ->
          begin
            match def.ty with 
            | Some ty -> (
                M.E.throw_if_some 
                  (fun _ -> Logging.(make_msg def.loc 
                    @@ Fmt.str "circular type declaration : %s" 
                    @@ String.concat " -> " (List.rev (def::path) |> List.map (fun ({name;_}:ty_defn) -> name)))
                  )
                  (List.find_opt (fun (d:ty_defn) -> d.name = def.name) path)
                
                >>= fun () -> let+ ((_,t),p) = aux ty (def::path) in t,p
              )
            | None -> (* abstract type *) 
              (* Logs.debug (fun m -> m "'%s' resolves to abstract type '%s' " (string_of_sailtype (Some ty)) def.name);  *)
              return (default (T ()),path)
          end
        | _ ->  return (default @@ unit_decl_of_decl def,path) (* must point to an enum or struct, nothing to resolve *)
      end
    in (l_ty,t),path
  in
  let+ res,p = aux ty [] in
  (* p only contains type_def from the current module *)
  let env = List.fold_left (fun env (td:ty_defn) -> D.update_decl td.name {td with ty=Some res} (Self Type) env) env p in 
  res,env

let check_non_cyclic_struct (name:string) (l,proto) env : unit M.E.t = 
  let rec aux id curr_loc (s:struct_proto) checked = 
    let* () = M.E.throw_if 
                Logging.(make_msg l
                ~hint:(Some (Some curr_loc,"Hint : try boxing this type"))
                @@ Fmt.str "circular structure declaration : %s" 
                @@ String.concat " -> " (List.rev (id::checked))
                
                )
                
                (List.mem id checked) in 
    let checked = id::checked in 
    ListM.iter (
      fun (_,(l,t,_)) -> match snd t with

      | CompoundType {name=_,name;origin=Some (_,origin); decl_ty = Some S ();_} -> 
        begin
          match D.find_decl name (Specific (origin,(Filter [S ()]))) env with
          | Some (S (_,d)) -> aux name l d checked
          | _ -> failwith "invariant : all compound types must have a correct origin and type at this step"
        end
      | CompoundType {origin=None;decl_ty=None;_} -> M.E.throw Logging.(make_msg l "follow type not called")
      | _ -> return ()
    ) s.fields
  in
  aux name l proto []

let rename_var_exp (f: string -> string) (e: _ AstHir.expression) = 
  let open AstHir in 
  let rec aux (e : _ expression) = 
    let buildExp = buildExp e.info in 
    match e.exp with 
    | Variable id -> buildExp @@ Variable (f id)
    | Deref e -> let e = aux e in buildExp @@ Deref e
    | StructRead (mod_loc,e, id) -> let e = aux e in buildExp @@ StructRead(mod_loc,e,id)
    | ArrayRead (e1, e2) ->
      let e1 = aux e1 in 
      let e2 = aux e2 in 
      buildExp @@ ArrayRead (e1,e2)
    | Literal _ as l -> buildExp l
    | UnOp (op, e) -> let e = aux e in buildExp @@ UnOp (op,e)
    | BinOp(op,e1,e2)->
      let e1 = aux e1 in 
      let e2 = aux e2 in
      buildExp @@ BinOp(op,e1,e2)
    | Ref (b, e) ->
      let e = aux e in buildExp @@ Ref(b,e)
    | ArrayStatic el -> let el = List.map aux el in buildExp @@ ArrayStatic el
    | StructAlloc (origin,id, m) -> let m = List.map (fun (n,(l,e)) -> n,(l,aux e)) m in buildExp @@ StructAlloc (origin,id,m)
    | EnumAlloc (id, el) -> let el = List.map aux el in buildExp @@ EnumAlloc (id,el)
    | MethodCall (mod_loc, id, el) -> let el  = List.map aux el in buildExp @@ MethodCall (mod_loc,id,el)
    in aux e
  
  let rename_var_stmt (f:string -> string) s = 
    let open AstHir in 
    let rec aux (s : _ statement) = 
      let buildStmt = buildStmt s.info in
      match s.stmt with
      | DeclVar (mut, id, opt_t,opt_exp) -> 
        let e = MonadOption.M.fmap  (rename_var_exp f) opt_exp in
        buildStmt @@ DeclVar (mut,f id,opt_t,e)
      | Assign(e1, e2) -> 
        let e1 = rename_var_exp f e1
        and e2 = rename_var_exp f e2 in 
        buildStmt @@ Assign(e1, e2)
      | Seq(c1, c2) -> 
        let c1 = aux c1 in
        let c2 = aux c2 in
        buildStmt  @@ Seq(c1, c2)
      | If(cond_exp, then_s, else_s) -> 
        let cond_exp = rename_var_exp f cond_exp in
        let then_s = aux then_s in
        let else_s  = MonadOption.M.fmap aux else_s in
        buildStmt (If(cond_exp, then_s, else_s))
      | Loop c -> let c = aux c in buildStmt (Loop c)
      | Break -> buildStmt Break
      | Case(e, _cases) -> let e = rename_var_exp f e in buildStmt (Case (e, []))
      | Invoke i -> 
        let args = List.map (rename_var_exp f) i.args in 
        let ret_var = MonadOption.M.fmap f i.ret_var in
        buildStmt @@ Invoke {i with ret_var;args}
      | Return e -> let e =  MonadOption.M.fmap (rename_var_exp f) e in buildStmt @@ Return e
      | Block c -> let c = aux c in buildStmt (Block c)
      | Skip -> buildStmt Skip
      in
      aux s


let resolve_names (sm : ('a,'b) SailModule.methods_processes SailModule.t)  =
  let module ES = struct 
    module S =  MonadState.M(struct type t = D.t end)
    include Logging.MakeTransformer(S)
    let update_env f = S.update f |> lift
    let set_env e = S.set e |> lift
    let get_env = S.get |> lift
  end 
  in
  let open UseMonad(ES) in
  let module TEnv = MakeFromSequencable(SailModule.DeclEnv.TypeSeq) in
  let module SEnv = MakeFromSequencable(SailModule.DeclEnv.StructSeq) in
  (* let module MEnv = F.MakeFromSequencable(SM.DeclEnv.MethodSeq) in
  let module PEnv = F.MakeFromSequencable(SM.DeclEnv.ProcessSeq) in *)
  let open SailModule.DeclEnv in

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
    {sm with body=SailModule.{methods; processes}; declEnv}
  ) sm.declEnv |> fst in
  sm