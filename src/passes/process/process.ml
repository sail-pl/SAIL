open Common
open TypesCommon
open IrHir
open SailParser
open ProcessUtils
module H = HirUtils
module HirS = AstHir.Syntax
module E = Error.Logger
open ProcessMonad
open Monad.UseMonad(M)

module Pass = Pass.Make(struct
  let name = "Process to Methods"
  type in_body = body
  type out_body = in_body

  let transform (sm:in_body SailModule.t) : out_body SailModule.t E.t = 
    let lower_processes (procs : (H.statement,H.expression) AstParser.process_body process_defn list) : _ method_defn E.t =
      let rec compute_tree closed (l,pi:loc * _ proc_init)  : H.statement M.t = 
        let closed = FieldSet.add pi.proc closed in (* no cycle *)
        let* p = M.throw_if_none Error.(make dummy_pos "unknown process") (List.find_opt (fun (p:_ process_defn) -> p.p_name = pi.proc) procs) in
        let* tag = M.fresh_prefix p.p_name in
        let prefix = (Fmt.str "%s_%s_" tag) in
        let read_params,write_params = p.p_interface.p_shared_vars in 
        let param_arg_mismatch name p a = 
          let pl,al = List.(length p,length a) in
          M.throw_if Error.(make l @@ Fmt.str "number of %s params provided and required differ : %i vs %i" name al pl) (pl <> al) in
        
        let* () = param_arg_mismatch "read" read_params pi.read in
        let* () = param_arg_mismatch "write" write_params pi.write in
        let* () = param_arg_mismatch "init" p.p_interface.p_params pi.params in


        let rename_l = List.map2 (fun (_,subx) (_,(x,_)) -> (x,subx) ) (pi.read @ pi.write) (fst p.p_interface.p_shared_vars @ snd p.p_interface.p_shared_vars) in
        let rename = fun id -> match List.assoc_opt id rename_l with Some v -> v | None -> id in 
        
        (* add process local (but persistant) vars *)
        ListM.iter (fun (l,(id,(_,ty))) ->
          let* ty,_ = HirUtils.follow_type ty sm.declEnv |> M.EC.lift |> M.ECW.lift |> M.lift  in
          M.(write_decls HirS.(var (l,prefix id,ty)))
        ) p.p_body.locals >>= fun () -> 

        let* params = ListM.fold_right2 (fun (p:param) arg params -> 
          let param = prefix p.id in 
          (* add process parameters to the decls *)
          M.(write_decls HirS.(var (p.loc,param,p.ty))) >>| fun () -> 
          HirS.(params && !@param = arg)
        ) p.p_interface.p_params pi.params M.SeqMonoid.empty in
        
        (* add process init *)
        let init = rename_var_stmt prefix p.p_body.init in 
        M.write_init HirS.(!! (params && init)) >>= fun () -> 
        
        
        (* inline process calls *)
        let rec aux ((_,s) : (H.statement, H.expression) AstParser.p_statement) (_ty:AstParser.pgroup_ty) : H.statement M.t =
          
          let process_cond c s = match c with Some c -> HirS.(_if (rename_var_exp prefix c) s skip) | None -> s in

          match s with
          | Statement (s,cond) -> 
            let s = rename_var_stmt (fun id -> let new_id = rename id in if new_id <> id then new_id else prefix id) s in
            return (process_cond cond s)
          
          | Run ((l,id),cond) ->
              M.throw_if Error.(make l "not allowed to call Main process explicitely") (id = Constants.main_process) >>= fun () ->
              M.throw_if Error.(make l "not allowed to have recursive process") (FieldSet.mem id closed) >>= fun () ->
              let* l,pi = M.throw_if_none Error.(make l @@ Fmt.str "no proc init called '%s'" id) (List.find_opt (fun (_,p: loc * _ proc_init) -> p.id = id) p.p_body.proc_init) in
              let read = List.map (fun (l,id) -> l,prefix id) pi.read in 
              let write = List.map (fun (l,id) -> l,prefix id) pi.write in 
              let params = List.map (rename_var_exp prefix) pi.params in
              compute_tree closed (l,{pi with read ; write ; params}) >>| process_cond cond

          | PGroup g -> 
            ListM.fold_right (fun child s  -> let+ res = aux child g.p_ty in HirS.(s && res)) g.children HirS.skip >>| process_cond g.cond
            
        in
        aux p.p_body.loop Parallel
      in
    
      let open Monad.MonadOperator(E) in
      (
        let* m = M.throw_if_none (Error.make dummy_pos "need main process") 
                                  (List.find_opt (fun p -> p.p_name = Constants.main_process) procs) 
        in 
        let (pi: _ proc_init) = {read = []; write = [] ; params = [] ; id = Constants.main_process ; proc = Constants.main_process} in
        let* body = compute_tree FieldSet.empty (dummy_pos,pi) in 
        let+ () = M.write_loop body in m
      ) |> M.run >>| fun x -> finalize x
  
  in
  let open Monad.UseMonad(E) in
  let+ main = lower_processes sm.body.processes in
  let body : in_body =  { methods = main::sm.body.methods; processes = sm.body.processes} in 
  {sm with body}
end)