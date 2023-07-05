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
      let rec compute_tree args closed (p : (H.statement,H.expression) AstParser.process_body process_defn)  : _ M.t = 
        let closed = FieldSet.add p.p_name closed in (* no cycle *)
        let* prefix = M.fresh_prefix p.p_name in
    
        (* add process local (but persistant) vars *)
        ListM.iter (fun (id,ty) ->
          let* ty,_ = HirUtils.follow_type ty sm.declEnv |> M.EC.lift |> M.lift  in
          M.(write_decls HirS.(var (dummy_pos,prefix ^ id,ty)))
        ) p.p_body.decls >>= fun () -> 

        let* params = ListM.fold_right2 (fun (p:param) arg params -> 
          let param = prefix ^ p.id in 
          (* add process parameters to the decls *)
          M.(write_decls HirS.(var (p.loc,param,p.ty))) >>| fun () -> 
          HirS.(params && !@param = arg)
        ) (fst p.p_interface) args M.SeqMonoid.empty in
        
        (* add process init *)
        let init = prefix_stmt prefix HirS.(!! (snd p.p_body.init)) in 
        M.write_init HirS.(!! (params && init)) >>= fun () -> 
          
        (* inline process calls *)
        let+ children,closed,body = ListM.fold_right ( fun new_b (ch,cl,b)  -> 
          let+ new_b,p,cl' = lower_body prefix closed new_b in 
          (match p with None -> ch | Some p -> p::ch), FieldSet.union cl cl',HirS.(b && new_b)
        ) p.p_body.loop ([],closed,M.SeqMonoid.empty)  in
    
        body,P (p,children),closed
    
      and lower_body prefix closed ((_l,b),cond) =
        let open AstParser in
        let when_on  = fun s -> match cond with
        | None -> s
        | Some cond -> HirS.(_if (prefix_exp prefix cond) s skip)
        in 
        
        match b with
        | Statement s -> return (when_on (prefix_stmt prefix s),None,FieldSet.empty)
        | Run ((l,id),args) -> 
          M.throw_if Error.(make l "not allowed to call Main process explicitely") (id = Constants.main_process) >>= fun () ->
          M.throw_if Error.(make l "not allowed to have recursive process") (FieldSet.mem id closed) >>= fun () ->
          let* p = M.throw_if_none Error.(make l @@ Fmt.str "unknown process %s" id) (List.find_opt (fun p -> p.p_name = id) procs) in
          let args = List.map (prefix_exp prefix) args in 
          compute_tree args closed p >>| fun (b,p,cl) -> when_on b,Some p,cl
        
      in
    
      let open Monad.MonadOperator(E) in
      (
        let* m = M.throw_if_none (Error.make dummy_pos "need main process") 
                                  (List.find_opt (fun p -> p.p_name = Constants.main_process) procs) 
        in 
        let* body,_t,_ = compute_tree [] FieldSet.empty m in 
        let+ () = M.write_loop body in m
      ) |> M.run >>| finalize
  
  in
  let open Monad.UseMonad(E) in
  let+ main = lower_processes sm.body.processes in
  let body : in_body =  { methods = main::sm.body.methods; processes = []} in 
  {sm with body}
end)