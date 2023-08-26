open Common
open TypesCommon
open Monad
open IrHir
module D = SailModule.Declarations

type expression = (loc * string, l_str) AstHir.expression (* string is the key for the type map *)
type statement = (loc,l_str,expression) AstHir.statement

module M = ThirMonad.Make(struct
  type t = statement
  let mempty : t = {info=dummy_pos; stmt=Skip}
  let mconcat : t -> t -> t = fun x y -> {info=dummy_pos; stmt=Seq (x,y)}
  end
)

open M
open UseMonad(M.ES)



let rec resolve_alias (l,ty : sailtype) : (sailtype,string) Either.t M.ES.t = 
  match ty with
  | CompoundType {origin;name=(_,name);decl_ty=Some (T ());_} -> 
    let* (_,mname) =  M.ES.throw_if_none Logging.(make_msg l @@ "unknown type '" ^ name ^ "' , all types must have an origin (problem with HIR)") origin in
    let* ty_t = M.ES.get_decl name (Specific (mname,Type))  
                >>= M.ES.throw_if_none Logging.(make_msg l @@ Fmt.str "declaration '%s' requires importing module '%s'" name mname) in 
    begin
    match ty_t.ty with
    | Some (_,CompoundType _ as ct) -> resolve_alias ct
    | Some t -> return (Either.left t)
    | None -> return (Either.right name) (* abstract type, only look at name *)
    end
  | _ -> return (Either.left (l,ty))
  
let string_of_sailtype_thir (t : sailtype option) : string M.ES.t = 
  let+ res = 
    match t with
    | Some (_,CompoundType {origin; name=(loc,x); _}) -> 
        let* (_,mname) = M.ES.throw_if_none Logging.(make_msg loc "no origin in THIR (problem with HIR)") origin in
        let+ decl = M.ES.(get_decl x (Specific (mname,Filter [E (); S (); T()])) 
                      >>=  throw_if_none Logging.(make_msg loc "decl is null (problem with HIR)")) in
        begin
          match decl with 
          | T ty_def -> 
          begin
            match ty_def.ty with
            | Some t -> Fmt.str " (= %s)" @@ string_of_sailtype (Some t) 
            | None -> "(abstract)"
          end
          | S (_,s) -> Fmt.str " (= struct <%s>)" (List.map (fun (n,(_,t,_)) -> Fmt.str "%s:%s" n @@ string_of_sailtype (Some t) ) s.fields |> String.concat ", ")
          | _ -> failwith "can't happen"
        end
    |  _ -> return ""
    in (string_of_sailtype t) ^ res


let matchArgParam (loc : loc) (arg:  sailtype) (m_param : sailtype) : sailtype  M.ES.t =
  let rec aux (a:sailtype) (m:sailtype) : sailtype M.ES.t = 
    let* lt = resolve_alias a in
    let* rt = resolve_alias m in

    match lt,rt with
    | Left (loc_l,l), Left (_,r) ->
      begin
        match l,r with
        | Bool, Bool -> return (loc_l,Bool)
        | (Int i1),  (Int i2) when i1 = i2 ->  return (loc_l,Int  i1) 
        | Float, Float -> return (loc_l,Float)
        | Char, Char -> return (loc_l,Char)
        | String, String -> return (loc_l,String)
        | ArrayType (at,s), ArrayType (mt,s') -> 
          if s = s' then
            let+ t = aux at mt in loc_l,ArrayType (t,s)
          else
            M.ES.throw Logging.(make_msg loc_l (Printf.sprintf "array length mismatch : wants %i but %i provided" s' s))

        | Box _at, Box _mt -> M.ES.throw Logging.(make_msg loc_l "todo box")

        | RefType (at,am), RefType (mt,mm) -> 
          if am <> mm then M.ES.throw Logging.(make_msg loc_l "different mutability") 
          else aux at mt
        
        | at, GenericType _ 
        | GenericType _, at  -> return (loc_l,at)

        | CompoundType c1,  CompoundType c2 when snd c1.name = snd c2.name ->
          return arg

        | _ -> let* param = string_of_sailtype_thir (Some m_param) and* arg = string_of_sailtype_thir (Some arg) in 
        M.ES.throw Logging.(make_msg loc_l @@ Printf.sprintf "wants %s but %s provided" param arg)
      end
    
    | Right name, Right name' -> 
      let+ () = M.ES.throw_if Logging.(make_msg loc @@ Fmt.str "want abstract type %s but abstract type %s provided" name name') (name <> name') in
      arg

  | _ -> let* param = string_of_sailtype_thir (Some m_param) 
          and* arg' = string_of_sailtype_thir (Some arg) in 
          M.ES.throw Logging.(make_msg loc @@ Printf.sprintf "wants %s but %s provided" param arg')
                              
  in aux arg m_param 


let check_binop op l r : string M.ES.t = 
  let* l_t = M.ES.get_type_from_id l 
  and* r_t = M.ES.get_type_from_id r in
  match op with
  | Lt | Le | Gt | Ge | Eq | NEq ->
    let* _ = matchArgParam (fst l_t) r_t l_t in M.ES.get_type_id (fst l_t,Bool)
  | And | Or -> 
    let* _ = matchArgParam (fst l_t) l_t (fst l_t,Bool)
    and* _ = matchArgParam (fst l_t) r_t (fst l_t,Bool) 
    in M.ES.get_type_id (fst l_t,Bool)
  | Plus | Mul | Div | Minus | Rem ->
    let+ _ = matchArgParam (fst l_t) r_t l_t in snd l


let check_call (name:string) (f : method_proto) (args: expression list) loc : unit M.ES.t =
    (* if variadic, we just make sure there is at least minimum number of arguments needed *)
    let args = if f.variadic then List.filteri (fun i _ -> i < (List.length f.args)) args else args in
    let nb_args = List.length args and nb_params = List.length f.args in
    M.ES.throw_if Logging.(make_msg loc (Printf.sprintf "unexpected number of arguments passed to %s : expected %i but got %i" name nb_params nb_args))
                (nb_args <> nb_params)
    >>= fun () -> 
    ListM.iter2 
    (
      fun (ca:expression) ({ty=a;_}:param) ->
        let* rty = M.ES.get_type_from_id ca.info in 
        let+ _ = matchArgParam (fst ca.info) rty a in ()
    ) args f.args
    




let find_function_source (fun_loc:loc) (_var: string option) (name : l_str) (import:l_str option) (el: expression list) : (l_str * D.method_decl) M.ES.t =
  let* (_,env),_ = M.ES.get in 
  let* mname,def = HirUtils.find_symbol_source ~filt:[M ()] name import env |> M.ES.lift in
  match def with 
  | M decl ->  
    let+ _ = check_call (snd name) (snd decl) el fun_loc in mname,decl
    (* let _x = fun_loc and _y = el in return (mname,decl) *)

  | _ -> failwith "non method returned" (* cannot happen because we only requested methods *)

        (* ES.throw 
                      @@ make_msg fun_loc ~hint:(Some (None,"specify one with '::' annotation")) 
                      @@ Fmt.str "multiple definitions for function %s : \n\t%s" id 
                        (List.map (
                          fun (i,((_,_,m):SailModule.Declarations.method_decl)) -> 
                            Fmt.str "from %s : %s(%s) : %s" i.mname id
                            (List.map (fun a -> Fmt.str "%s:%s" a.id (string_of_sailtype (Some a.ty))) m.args |> String.concat ", ") 
                            (string_of_sailtype m.ret)
                        ) choice |> String.concat "\n\t") *)
                        
let find_struct_source (name: l_str) (import : l_str option) : (l_str * D.struct_decl) M.ES.t =
  let* (_,env),_ = M.ES.get in 
  let+ origin,def = HirUtils.find_symbol_source ~filt:[S()] name import env |> M.ES.lift in
  begin
    match def with 
    | S decl -> origin,decl
    | _ -> failwith "non struct returned"
  end




  let resolve_types (sm : ('a,'b) SailModule.methods_processes SailModule.t)  =
    let open HirUtils in
    
    let module ES = struct 
      module T = struct type t = {decls: D.t ; types : Env.TypeEnv.t} end
      module S =  MonadState.M(T)
      include Logging.MakeTransformer(S)
      let update_env f = S.update f |> lift
      let set_env e = S.set e |> lift
      let get_env = S.get |> lift
    end 
    in
    let open UseMonad(ES) in
    let module TEnv = MakeFromSequencable(SailModule.DeclEnv.TypeSeq) in
    let module SEnv = MakeFromSequencable(SailModule.DeclEnv.StructSeq) in
    let open SailModule.DeclEnv in

    (* resolving aliases *)
    let sm = (
    
      let* env = ES.get_env in 

      let* () = 
      TEnv.iter (
        fun (id,({ty; _} as def))  -> 
          let* ty = match ty with 
          | None -> return None 
          | Some t -> 
            let* env = ES.get_env in 
            let* t,decls = (follow_type t env.decls) |> ES.S.lift in
            let+ () = ES.set_env {env with decls} in Some t
          in
          ES.update_env (fun e -> {e with decls=update_decl id {def with ty} (Self Type) e.decls})
      ) (get_own_decls env.decls |> get_decls Type) in

      let* env = ES.get_env in 
      
      let* () = SEnv.iter (
        fun (id,(l,{fields; generics}))  -> 
          let* fields = ListM.map (
            fun (name,(l,t,n)) -> 
              let* env = ES.get_env in 
              let* t,decls = (follow_type t env.decls) |> ES.S.lift in
              let+ () = ES.set_env {env with decls} in 
              name,(l,t,n)
          ) fields
          in
          let proto = l,{fields;generics} in 
          ES.update_env (fun e -> {e with decls=update_decl id proto (Self Struct) e.decls})
      ) (get_own_decls env.decls |> get_decls Struct)
      in

      let* methods = ListM.map (
        fun ({m_proto;m_body} as m) -> 
          let* rtype = match m_proto.rtype with 
          | None -> return None 
          | Some t -> 
            let* env = ES.get_env in 
            let* t,decls = (follow_type t env.decls) |> ES.S.lift in
            let+ () = ES.set_env {env with decls} in Some t
          in
          let* params = ListM.map (
            fun (({ty;_}:param) as p) -> 
              let* env = ES.get_env in 
              let* ty,decls = (follow_type ty env.decls) |> ES.S.lift in
              let+ () = ES.set_env {env with decls} in {p with ty}
          ) m_proto.params in
          let m = {m with m_proto={m_proto with params; rtype}} in 
          let true_name = (match m_body with Left (sname,_) -> sname | Right _ -> m_proto.name) in
          let+ () = ES.update_env 
            (fun e -> 
              let decls = update_decl m_proto.name ((m_proto.pos,true_name), defn_to_proto (Method m)) (Self Method) e.decls in
              {e with decls}
            ) 
          in m
      ) sm.body.methods in

      let+ processes = ListM.map (
        fun proc ->
          let* p_params = ListM.map (
            fun (({ty;_}:param) as p) -> 
              let* env = ES.get_env in 
              let* ty,decls = (follow_type ty env.decls) |> ES.S.lift in
              let+ () = ES.set_env {env with decls} in {p with ty}
          ) proc.p_interface.p_params in
        let p = {proc with p_interface={proc.p_interface with p_params}} in
        let+ () = ES.update_env (fun e -> {e with decls=update_decl p.p_name (p.p_pos, defn_to_proto (Process p)) (Self Process) e.decls}) 
        in p
      ) sm.body.processes in 


      {sm with body=SailModule.{methods; processes}; declEnv=env.decls; typeEnv=env.types}

    ) {decls=sm.declEnv;types=sm.typeEnv} |> fst in
    sm