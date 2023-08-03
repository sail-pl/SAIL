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
      let rec compute_tree closed (pi:_ proc_init)  : _ M.t = 
        let closed = FieldSet.add pi.proc closed in (* no cycle *)
        let* p = M.throw_if_none Error.(make dummy_pos "unknown process") (List.find_opt (fun (p:_ process_defn) -> p.p_name = pi.proc) procs) in
        let* tag = M.fresh_prefix p.p_name in
        let prefix = (String.cat tag) in
        let rename_l = List.map2 (fun (_,subx) (_,x) -> (x,subx) ) (pi.read @ pi.write) (fst p.p_interface.p_shared_vars @ snd p.p_interface.p_shared_vars) in
        let rename = fun id -> match List.assoc_opt id rename_l with Some v -> v | None -> id in 
        
        (* add process local (but persistant) vars *)
        ListM.iter (fun (l,(id,(_,ty))) ->
          let* ty,_ = HirUtils.follow_type ty sm.declEnv |> M.EC.lift |> M.lift  in
          M.(write_decls HirS.(var (l,tag ^ id,ty)))
        ) p.p_body.locals >>= fun () -> 

        let* params = ListM.fold_right2 (fun (p:param) arg params -> 
          let param = tag ^ p.id in 
          (* add process parameters to the decls *)
          M.(write_decls HirS.(var (p.loc,param,p.ty))) >>| fun () -> 
          HirS.(params && !@param = arg)
        ) p.p_interface.p_params pi.params M.SeqMonoid.empty in
        
        (* add process init *)
        let init = rename_var_stmt prefix p.p_body.init in 
        M.write_init HirS.(!! (params && init)) >>= fun () -> 
          
        (* inline process calls *)
        let rec aux ((_,s) : (H.statement, H.expression) AstParser.p_statement) : _ M.t =
          match s with
          | PSeq (p1,p2) -> let+ p1 = aux p1 and* p2 = aux p2 in HirS.(p1 && p2)
          
          | PPar (p1,p2) -> let+ p1 = aux p1 and* p2 = aux p2 in HirS.(p1 && p2)
          
          | Statement s -> return (rename_var_stmt (fun id -> let new_id = rename id in if new_id <> id then new_id else tag ^ id) s)
          
          | Run (l,id) ->
              M.throw_if Error.(make l "not allowed to call Main process explicitely") (id = Constants.main_process) >>= fun () ->
              M.throw_if Error.(make l "not allowed to have recursive process") (FieldSet.mem id closed) >>= fun () ->
              let* pi = M.throw_if_none Error.(make l @@ Fmt.str "no proc init called '%s'" id) (List.find_opt (fun (p: _ proc_init) -> p.id = id) p.p_body.proc_init) in
              let read = List.map (fun (l,id) -> l,tag ^ id) pi.read in 
              let write = List.map (fun (l,id) -> l,tag ^ id) pi.write in 
              let params = List.map (rename_var_exp prefix) pi.params in
              compute_tree closed {pi with read ; write ; params}
          | PGroup (c,s) -> 
            let+ s = aux s in
            begin
            match c with 
            | Some c -> HirS.(_if (rename_var_exp prefix c) s skip)
            | None -> s
            end
          | PSkip -> return HirS.skip
        in
        aux p.p_body.loop
      in
    
      let open Monad.MonadOperator(E) in
      (
        let* m = M.throw_if_none (Error.make dummy_pos "need main process") 
                                  (List.find_opt (fun p -> p.p_name = Constants.main_process) procs) 
        in 
        let (pi: _ proc_init) = {read = []; write = [] ; params = [] ; id = Constants.main_process ; proc = Constants.main_process} in
        let* body = compute_tree FieldSet.empty pi in 
        let+ () = M.write_loop body in m
      ) |> M.run >>| finalize
  
  in
  let open Monad.UseMonad(E) in
  let+ main = lower_processes sm.body.processes in
  let body : in_body =  { methods = main::sm.body.methods; processes = []} in 
  {sm with body}
end)