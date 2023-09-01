open Common
open TypesCommon
open IrHir
open SailParser
open ProcessUtils
module HirU = HirUtils
module AstU = IrAst.Utils
module HirS = IrAst.Ast.Syntax
module E = Logging.Logger
open ProcessMonad
open Monad.UseMonad(M)

module Pass = Pass.Make(struct
  let name = "Process to Methods"
  type in_body = body
  type out_body = in_body

  let transform (sm:in_body SailModule.t) : out_body SailModule.t E.t = 
    let lower_processes (procs : (HirU.statement,HirU.expression) AstParser.process_body process_defn list) : _ method_defn E.t =
      let rec compute_tree closed (l,pi:loc * _ proc_init)  : HirU.statement M.t = 
        let closed = FieldSet.add pi.proc closed in (* no cycle *)

        let* p = find_process_source (mk_locatable l pi.proc) pi.mloc procs (*fixme : grammar to allow :: syntax *) in
        let* p = M.throw_if_none Logging.(make_msg l @@ Fmt.str "process '%s' is unknown" pi.proc) p in
        let* tag = M.fresh_prefix p.p_name in
        let prefix = (Fmt.str "%s_%s_" tag) in
        let read_params,write_params = p.p_interface.p_shared_vars in 
        let param_arg_mismatch name p a = 
          let pl,al = List.(length p,length a) in
          M.throw_if Logging.(make_msg l @@ Fmt.str "number of %s params provided and required differ : %i vs %i" name al pl) (pl <> al) in
        
        let* () = param_arg_mismatch "read" read_params pi.read in
        let* () = param_arg_mismatch "write" write_params pi.write in
        let* () = param_arg_mismatch "init" p.p_interface.p_params pi.params in


        let rename_l = List.map2 (fun subx x -> (fst x.value,subx.value) ) 
          (pi.read @ pi.write) 
          (fst p.p_interface.p_shared_vars @ snd p.p_interface.p_shared_vars) in
        let rename = fun id -> match List.assoc_opt id rename_l with Some v -> v | None -> id in 
        
        (* add process local (but persistant) vars *)
        ListM.iter (fun (id,ty) ->
          let* ty,_ = HirUtils.follow_type ty sm.declEnv |> M.EC.lift |> M.ECW.lift |> M.lift  in
          M.(write_decls HirS.(var l (prefix id.value) ty None))
        ) p.p_body.locals >>= fun () -> 

        let* params = ListM.fold_right2 (fun (p:param) arg params -> 
          let param = prefix p.id in 
          (* add process parameters to the decls *)
          M.(write_decls HirS.(var p.loc param p.ty None)) >>| fun () -> 
          HirS.(params && !@param = arg)
        ) p.p_interface.p_params pi.params M.SeqMonoid.empty in
        
        (* add process init *)
        let init = IrAst.Utils.rename_var prefix p.p_body.init in 
        M.write_init HirS.(!! (params && init)) >>= fun () -> 
        
        
        (* inline process calls *)
        let rec aux (stmt : (HirU.statement, HirU.expression) AstParser.p_statement) (_ty:AstParser.pgroup_ty) : HirU.statement M.t =
          let replace_or_prefix = fun id -> let new_id = rename id in if new_id <> id then new_id else prefix id in
          let process_cond c s = match c with Some c -> HirS.(if_ (AstU.rename_var replace_or_prefix c) s (skip ())) | None -> s in

          match stmt.value with
          | Statement (s,cond) -> 
            let s = AstU.rename_var replace_or_prefix s in
            return (process_cond cond s)
          
          | Run (id,cond) ->
              M.throw_if Logging.(make_msg l "not allowed to call Main process explicitely") (id.value = Constants.main_process) >>= fun () ->
              M.throw_if Logging.(make_msg l "not allowed to have recursive process") (FieldSet.mem id.value closed) >>= fun () ->
              let* pi = M.throw_if_none Logging.(make_msg l @@ Fmt.str "no proc init called '%s'" id.value) 
                          (List.find_opt (fun p -> p.value.id = id.value) p.p_body.proc_init) in
              let read = List.map (fun (id:l_str) -> mk_locatable id.loc @@ prefix id.value) pi.value.read in 
              let write = List.map (fun (id:l_str) -> mk_locatable id.loc @@ prefix id.value) pi.value.write in 
              let params = List.map (AstU.rename_var prefix) pi.value.params in
              compute_tree closed (l,{pi.value with read ; write ; params}) >>| process_cond cond

          | PGroup g -> 
            ListM.fold_right (fun child s  -> let+ res = aux child g.p_ty in HirS.(s && res)) g.children (HirS.skip ()) >>| process_cond g.cond
            
        in
        aux p.p_body.loop Parallel
      in
    
      let open Monad.MonadOperator(E) in
      (
        let* m = M.throw_if_none Logging.(make_msg dummy_pos "need main process") 
                                  (List.find_opt (fun p -> p.p_name = Constants.main_process) procs) 
        in 
        let (pi: _ proc_init) = {mloc=None; read = []; write = [] ; params = [] ; id = Constants.main_process ; proc = Constants.main_process} in
        let* body = compute_tree FieldSet.empty (dummy_pos,pi) in 
        let+ () = M.write_loop body in m
      ) |> M.run sm.declEnv >>| finalize
  
  in
  let open Monad.UseMonad(E) in
  let* main = lower_processes sm.body.processes in
  let body : in_body =  { methods = main::sm.body.methods; processes = sm.body.processes} in 
  let decl = SailModule.method_decl_of_defn main in 
  let+ declEnv = SailModule.DeclEnv.add_decl "main" decl Method sm.declEnv in
  {sm with body ; declEnv}
end)