open Common
open Monad
open TypesCommon
module E = Common.Logging
open Monad.MonadSyntax (E.Logger)
open IrMir.MirAst
open MonomorphizationMonad
module M = MonoMonad
open MonomorphizationUtils
open UseMonad(M)

module Pass = Pass.Make (struct
  let name = "Monomorphization"

  type in_body = (MonomorphizationUtils.in_body,(IrHir.HirUtils.statement,IrHir.HirUtils.expression) SailParser.AstParser.process_body) SailModule.methods_processes
  type out_body = MonomorphizationUtils.out_body

  module Env = SailModule.DeclEnv

  let mono_fun (f : sailor_function) (sm : in_body SailModule.t) : unit M.t =
    
    let mono_exp (exp : expression) (decls :declaration list) : sailtype M.t =
      let rec aux (exp : expression) : sailtype M.t =
        match exp.node with
        | Variable s -> 
          M.get_var s 
          <&> (function 
              | Some v -> Some (snd v).ty (* var is a function param *)
              | None -> Option.bind (List.find_opt (fun v -> v.id = s) decls) (fun decl -> Some decl.varType) (* var is function declaration *)
              ) 
          >>= M.throw_if_none Logging.(make_msg exp.tag.loc @@ Fmt.str "compiler error : var '%s' not found" s)
          
        | Literal l -> return (sailtype_of_literal l)
    
        | ArrayRead a -> 
          begin
            let* t = aux a.array in
            match t.value with
            | ArrayType (t, _) ->
                let+ idx_t = aux a.idx in
                let _ = resolveType idx_t (mk_locatable t.loc @@ Int 32) [] [] in
                t
            | _ -> failwith "cannot happen"
            end
        | UnOp (_, e) -> aux e
    
        | BinOp bop ->
            let* left = aux bop.left in
            let+ right = aux bop.right in
            let _ = resolveType left right [] [] in
            left
    
        | Ref (m, e) ->
            let+ t = aux e in
            mk_locatable exp.tag.loc @@ RefType (t, m)
    
        | Deref e -> (
            let+ t = aux e in
            match t.value with
            | RefType _ -> t
            | _ -> failwith "cannot happen"
          )
    
        | ArrayStatic (e :: h) ->
          let* t = aux e in 
          let+ t =
            ListM.fold_left (fun last_t e ->
                let+ next_t = aux e in
                let _ = resolveType next_t last_t [] [] in
                next_t
              ) t h
          in
          mk_locatable exp.tag.loc @@ ArrayType (t, List.length (e :: h))
    
        | ArrayStatic [] -> failwith "error : empty array"
        | StructAlloc2 _ -> failwith "todo: struct alloc"
        | EnumAlloc (_, _) -> failwith "todo: enum alloc"
        | StructRead2 _ -> failwith "todo: struct read"
      in
      aux exp
    in
    
    let construct_call (calle : string) (el : expression list) decls : (string * sailtype option) M.t =
      (* we construct the types of the args (and collect extra new calls) *)
      Logs.debug (fun m -> m "contructing call to %s from %s" calle f.m_proto.name);
      let* monos = M.get_monos and* funs = M.get_funs in
      Logs.debug (fun m -> m "current monos : %s" (String.concat ";" (List.map ( fun (g,(t:sailor_args)) -> g ^ " -> " ^ (List.map (fun (id,t) -> "(" ^ id ^ "," ^ string_of_sailtype (Some t) ^ ")") t |> String.concat "," )) monos)));
      Logs.debug (fun m -> m "current funs : %s" (FieldMap.fold (fun name _ acc -> Fmt.str "%s;%s" name acc)  funs ""));


      let* call_args =
        ListM.fold_left
          (fun l e ->
            Logs.debug (fun m -> m "analyze param expression");
            let* t = mono_exp e decls in 
            Logs.debug (fun m -> m "param is %s " @@ string_of_sailtype @@ Some t);
            return (t :: l)
          )
          [] el
      in
    
      (*don't do anything if the function is already added *)
      let mname = mangle_method_name calle call_args in
      let* funs = M.get_funs in
      match FieldMap.find_opt mname funs with
      | Some f ->
        Logs.debug (fun m -> m "function %s already discovered, skipping" calle);
        return (mname,f.methd.m_proto.rtype)
      | None -> 
        begin
          let* f = find_callable calle sm |> M.lift in
          match f with 
          | None -> (*import *) return (mname,Some (mk_locatable dummy_pos @@ Int 32) (*fixme*))
          | Some f -> 
            begin
              Logs.debug (fun m -> m "found call to %s, variadic : %b" f.m_proto.name f.m_proto.variadic );
              match f.m_body with
              | Right _ ->
                (* process and method 
        
                  we make sure they correspond to what the callable wants 
                  if the callable is generic we check all the generic types are present at least once 
                
                    we build a (string*sailtype) list of generic to type correspondance
                    if the generic is not found in the list, we add it with the corresponding type
                    if the generic already exists with the same type as the new one, we are good else we fail
                *)
                let* resolved_generics = check_args call_args f |> M.lift in
                List.iter (fun (n, t) -> Logs.debug (fun m -> m "resolved %s to %s " n (string_of_sailtype (Some t)))) resolved_generics;
        
                let* () = M.push_monos calle resolved_generics in
        
                let* rtype =
                  match f.m_proto.rtype with
                  | Some t -> 
                    (* Logs.warn (fun m -> m "TYPE BEFORE : %s" (string_of_sailtype (Some t)));  *)
                    let+ t = (degenerifyType t resolved_generics|> M.lift) in 
                  (* Logs.warn (fun m -> m "TYPE AFTER : %s" (string_of_sailtype (Some t)));  *)
                    Some t
                  | None -> return None
                in
                
                let params = List.map2 (fun (p:param) ty -> {p with ty}) f.m_proto.params call_args in
                let name = mname in
                let methd = { f with m_proto = { f.m_proto with rtype ; params } } in 
                let+ () = 
                  let* f = M.get_decl name (Self Method) in
                  if Option.is_none f  then   
                    M.add_decl name ((mk_locatable dummy_pos name),(defn_to_proto (Method methd))) Method
                  else return ()
                in
                mname,rtype
              | Left _ -> (* external method *) return (calle,f.m_proto.rtype)
            end
      end
    in

    let mono_body (lbl: label) (blocks : (VE.t,unit) basicBlock BlockMap.t) (decls : declaration list) : (_,_) basicBlock BlockMap.t MonoMonad.t =
      let rec aux lbl (treated: LabelSet.t) blocks = 
        (* collect calls and name correctly *)
        if LabelSet.mem lbl treated then return (treated,blocks)
        else
        begin
            let treated = LabelSet.add lbl treated in 

            let bb = BlockMap.find lbl blocks in
            let* () = M.set_ve bb.forward_info in 
            let* () = ListM.iter (fun assign -> mono_exp assign.target decls >>= fun _ty -> mono_exp assign.expression decls >>| fun _ty -> ()) bb.assignments 
            in
            let* terminator = M.throw_if_none Logging.(make_msg bb.location @@ Fmt.str "no terminator for bb%i : mir is broken.." lbl) bb.terminator in
            match terminator with 
            | Return e -> 
              let+ _ = 
              begin
                match e with 
                | Some e -> let+ t = mono_exp e decls in Some t
                | None -> return None
              end 
              in treated,blocks

            | Invoke new_f ->
              let* (id,_) = construct_call new_f.id new_f.params decls in
              aux new_f.next treated BlockMap.(update lbl (fun _ -> Some {bb with terminator=Some (Invoke {new_f with id})}) blocks)
            
            | Goto lbl -> aux lbl treated blocks

            | SwitchInt si -> 
              let* _ = mono_exp si.choice decls in 
              let* treated,blocks = aux si.default treated blocks in 
              ListM.fold_left ( fun (treated,blocks) (_,lbl) ->
                aux lbl treated blocks
              ) (treated,blocks) si.paths

            | Break -> failwith "no break should be there"
        end
      in aux lbl LabelSet.empty blocks <&> snd
    in
    match f.m_body with
    | Right (decls,cfg) -> 
      let* blocks = mono_body cfg.input cfg.blocks decls in
      let params = List.map (fun (p:param)  -> p.ty) f.m_proto.params in
      let name = mangle_method_name f.m_proto.name params in
      let methd = {m_proto = f.m_proto; m_body=Right (decls,{cfg with blocks})} in 
      M.add_fun name {methd; generics=[]}
      
    | Left _ -> (* external *) return ()


  let analyse_functions (sm : in_body SailModule.t) : unit M.t =

    (* find the function, apply generic substitutions to its signature and monomorphize *)
    let find_fun_and_mono (name, (g : sailor_args)) : unit M.t =
      let* f = find_callable name sm |> M.lift in
      match f with 
      | None -> (* fixme imports *) return ()
      | Some f -> 
        (* monomorphize signature with resolved generics (if any) *)
        let* params = ListM.map (fun (p : param) -> let+ ty = degenerifyType p.ty g  |> M.lift in {p with ty}) f.m_proto.params in
        let* rtype =
          match f.m_proto.rtype with
          | Some t -> let+ t = degenerifyType t g |> M.lift in Some t
          | None -> return None
        in
        (* update function signature *)
        let f = { f with m_proto = { f.m_proto with params; rtype } } in
        (* monomorphize, updating env with any new function calls found *)
        mono_fun f sm
    in

    let rec aux () : unit M.t =
      let* empty = M.get_monos >>| (=) [] in
      if not empty then  (* runs until no more new monomorphic function is found *)
      begin
        let* name,args = M.pop_monos in 
        Logs.debug (fun m -> m "looking at function %s with args %s " name (List.map (fun (_,t) -> string_of_sailtype @@ Some t) args |> String.concat " "));
        
        let mname = mangle_method_name name (List.split args |> snd) in

        (* we only look at untreated functions *)
        let* funs = M.get_funs in
        match FieldMap.find_opt mname funs with
        | Some _ ->
            Logs.debug (fun m -> m "%s already checked" mname);
            return ()
        | None ->
            Logs.debug (fun m -> m "analyzing monomorphic function %s" mname);
            find_fun_and_mono (name, args) >>= aux 
      end
      else return ()
    in
    let* _empty = M.get_monos >>| (=) [] in 
    (* M.throw_if Logging.(make_msg dummy_pos "no monomorphic callable (no main?)") empty  >>= *) 
    aux ()


  let transform (smdl : in_body SailModule.t) : out_body SailModule.t E.t =
    let add_if_mono name args gens else_ret =
      let args = List.map (fun (p:param) -> p.id,p.ty) args in
      if gens <> [] then M.pure [else_ret] else M.push_monos name args >>| fun () -> [] 
    in

    
    let mono_poly = (* add monomorphics to the env and collect generic methods *)
      M.pure []
      (* our entry points are non generic methods and processes *)
      >>= fun l -> ListM.fold_left (fun acc m -> add_if_mono m.m_proto.name m.m_proto.params m.m_proto.generics m >>| Fun.flip List.append acc) l smdl.body.methods
      (* 
        analyze them, find and resolve calls to generic functions 
        IMPORTANT : we must keep the generic functions : if one of them
        is called from an other module and we don't have a monomorphic versio, we must generate one using the generic version
       *)
      >>= fun l -> analyse_functions smdl >>| fun () -> l
    in

    let open MonadSyntax(E) in
    let+ polymorphics,mono_env = M.run smdl.declEnv mono_poly in
    Logs.info (fun m -> m "generated %i monomorphic functions : " (List.length (FieldMap.bindings mono_env.functions)));
    FieldMap.iter print_method_proto mono_env.functions;
    let monomorphics =  List.filter (fun m -> Either.is_left m.m_body) smdl.body.methods |> FieldMap.fold (fun name f acc -> {f.methd with m_proto={f.methd.m_proto with name}}::acc) mono_env.functions in

    {smdl with body={monomorphics;polymorphics;processes=smdl.body.processes}}
end)