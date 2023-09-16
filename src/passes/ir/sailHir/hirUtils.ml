open Common
open TypesCommon
open Monad
open SailParser
open IrAst

type hir = <resolvedImports : Ast.no; methodCall : Ast.yes; typedDeclVar:Ast.no>

type expression = (loc,Ast.exp,hir) Ast.generic_ast
type statement = (loc,Ast.stmt,hir) Ast.generic_ast

module M = HirMonad.Make( struct
  type t = statement
  let mempty = Ast.buildStmt dummy_pos Skip
  let mconcat = fun x y -> Ast.buildStmt dummy_pos (Seq (x,y))
  end
)

open M
module D = SailModule.DeclEnv

let lower_expression (exp : AstParser.expression) : expression M.t = 
  let open UseMonad(M) in
  let rec aux (exp : AstParser.expression) : expression M.t  = 
    let open Ast in 
    let v = match exp.value with 
      | Variable id -> 
        let* v = (M.ECS.find_var id |> M.lift) in
        M.throw_if_none Logging.(make_msg exp.loc @@ Fmt.str "undeclared variable '%s'" id)  v >>| fun _ ->
        Variable id

      | Deref e -> 
        let+ e = aux e in Deref e

      | StructRead (e, field) ->
        let+ strct = aux e in StructRead {import=None;value={field;strct}}

      | ArrayRead (array, idx) ->
        let+ array = aux array 
        and* idx = aux idx in 
        ArrayRead {array;idx}

      | Literal l -> return @@ Literal l

      | UnOp (op, e) -> 
        let+ e = aux e in UnOp (op, e)

      | BinOp(op,left,right)->
        let+ left = aux left
        and* right = aux right in
        BinOp {op;left;right}

      | Ref (m,e) -> let+ e = aux e in Ref (m,e)

      | ArrayStatic el ->  let+ el = ListM.map aux el in ArrayStatic el

      | StructAlloc (import,name,fields) ->
        let fields' = List.sort_uniq (fun (id1,_) (id2,_) -> String.compare id1 id2) fields in
        let* () = M.throw_if Logging.(make_msg exp.loc "duplicate fields") List.(length fields <> length fields') in
        let+ fields = ListM.map (pairMap2 (fun e -> let+ value = aux e.value in {e with value})) fields' in
        StructAlloc (mk_importable import {name;fields})

      | EnumAlloc (id, el) -> let+ el = ListM.map aux el in EnumAlloc (id, el)

        
      | MethodCall (import, id, args) -> let+ args = ListM.map aux args in MethodCall (mk_importable import {id;args;ret_var=None})
      
    in v <&> buildExp exp.loc
  in aux exp


open UseMonad(M.E)

let find_symbol_source ?(filt = [E (); S (); T ()] ) (id: l_str) (import : l_str option) (env : D.t) : (l_str * D.decls)  M.E.t =
  match import with
  | Some iname -> 
    if iname.value = Constants.sail_module_self || iname.value = D.get_name env then 
        let+ decl = 
          D.find_decl id.value (Self (Filter filt)) env 
          |> M.E.throw_if_none Logging.(make_msg id.loc @@ "no declaration named '" ^ id.value ^ "' in current module ")
        in
        {iname with value=D.get_name env},decl
    else
      let+ t = 
        M.E.throw_if_none Logging.(make_msg iname.loc ~hint:(Some (None,Fmt.str "try importing the module with 'import %s'" iname.value)) @@ "unknown module " ^ iname.value)  
                        (List.find_opt (fun {mname;_} -> mname = iname.value) (D.get_imports env)) >>= fun _ ->
        M.E.throw_if_none Logging.(make_msg id.loc @@ "declaration "  ^ id.value ^ " not found in module " ^ iname.value)
                        (D.find_decl id.value (Specific (iname.value, Filter filt)) env)
      in
    iname,t
  | None -> (* find it ourselves *)
    begin
      let decl = D.find_decl id.value (All (Filter filt)) env in
      match decl with
      | [i,m] -> 
        (* Logs.debug (fun m -> m "'%s' is from %s" id i.mname); *)
        return (mk_locatable dummy_pos i.mname,m)

      | [] ->  M.E.throw Logging.(make_msg id.loc @@ "unknown declaration " ^ id.value)

      | _ as choice -> M.E.throw 
                    @@ Logging.make_msg id.loc ~hint:(Some (None,"specify one with '::' annotation")) 
                    @@ Fmt.str "multiple definitions for declaration %s : \n\t%s" id .value
                      (List.map (fun (i,def) -> match def with T def -> Fmt.str "from %s : %s" i.mname (string_of_sailtype (def.ty)) | _ -> "") choice |> String.concat "\n\t")
  end

let follow_type ty env : (sailtype * D.t) M.E.t = 
  let current = SailModule.DeclEnv.get_name env in

  (* Logs.debug (fun m -> m "following type '%s'" (string_of_sailtype (Some ty))); *)

  let rec aux ty path : (sailtype * ty_defn list) M.E.t = 
    (* Logs.debug (fun m -> m "path: %s" (List.map (fun ({name;_}:ty_defn) -> name)path |> String.concat " ")); *)
    let+ (t,path : sailtype_ * ty_defn list) = 
      match ty.value with 
      
      | ArrayType (t,n) -> let+ t,path = aux t path in  ArrayType (t,n),path
      | Box t -> let+ t,path = aux t path in Box t,path
      | RefType (t,mut) -> let+ t,path = aux t path in RefType (t,mut),path
      | Bool | Char | Int _ | Float | String | GenericType _ as t ->  (* basic type, stop *)
        (* Logs.debug (fun m -> m "'%s' resolves to '%s'" (string_of_sailtype (Some ty)) (string_of_sailtype (Some ty'))); *)
        return (t,path)
      | CompoundType {origin;name=id;generic_instances;_} -> (* compound type, find location and definition *) 
      let* origin,def = find_symbol_source id origin env in 
      let default = fun ty -> CompoundType {origin=Some origin;name=id; generic_instances;decl_ty=Some ty} in 
      begin
        match def with
        | T def when origin.value = current ->
          begin
            match def.ty with 
            | Some ty -> (
                M.E.throw_if_some 
                  (fun _ -> Logging.(make_msg def.loc 
                    @@ Fmt.str "circular type declaration : %s" 
                    @@ String.concat " -> " (List.rev (def::path) |> List.map (fun ({name;_}:ty_defn) -> name)))
                  )
                  (List.find_opt (fun (d:ty_defn) -> d.name = def.name) path)
                
                >>= fun () -> let+ (t,p) = aux ty (def::path) in t.value,p
              )
            | None -> (* abstract type *) 
              (* Logs.debug (fun m -> m "'%s' resolves to abstract type '%s' " (string_of_sailtype (Some ty)) def.name);  *)
              return (default (T ()),path)
          end
        | _ ->  return (default @@ unit_decl_of_decl def,path) (* must point to an enum or struct, nothing to resolve *)
      end
    in {ty with value=t},path
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
      fun (_,{value=(ty,_);_}) -> match ty.value with

      | CompoundType {name;origin=Some origin; decl_ty = Some S ();_} -> 
        begin
          match D.find_decl name.value (Specific (origin.value,(Filter [S ()]))) env with
          | Some (S (_,d)) -> aux name.value l d checked
          | _ -> failwith "invariant : all compound types must have a correct origin and type at this step"
        end
      | CompoundType {origin=None;decl_ty=None;_} -> M.E.throw Logging.(make_msg l "follow type not called")
      | _ -> return ()
    ) s.fields
  in
  aux name l proto []


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
          fun (name,({value=(t,i);_} as f)) -> 
            let* env = ES.get_env in 
            let* t,env = (follow_type t env) |> ES.S.lift in
            let+ () = ES.set_env env in 
            name,{f with value=t,i}
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
        let+ () = ES.update_env (update_decl m_proto.name (mk_locatable m_proto.pos true_name, defn_to_proto (Method m)) (Self Method)) 
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