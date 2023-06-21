open AstMir
open IrThir
open Common 
open TypesCommon
open Monad
open MirMonad
open MirUtils

open MonadSyntax(ESC)
open MonadOperator(ESC)
open MonadFunctions(ESC) 


open Pass

module Pass = MakeFunctionPass(V)(
struct
  let name = "MIR"
  
  type in_body = Thir.Pass.out_body
  type out_body = mir_function

  let rec lexpr (e : Thir.expression) : expression ESC.t = 
    let open IrHir.AstHir in
    let lt = e.info in 
    match e.exp with 
      | Variable name ->
        let* id = find_scoped_var name in
        let+ () = ESC.update_var (fst lt) id assign_var in buildExp lt (Variable id)
      | Deref e -> rexpr e 
      | ArrayRead (e1, e2) -> let+ e1' = lexpr e1 and* e2' = rexpr e2 in buildExp lt (ArrayRead(e1',e2'))
      | StructRead (e,field) -> let+ e = lexpr e in buildExp lt (StructRead (e,field))
      | Ref _ -> ESC.error @@ Error.make (fst lt) "todo"
      |  _ ->  ESC.error @@ Error.make (fst lt) @@ "thir didn't lower correctly this expression" 
  and rexpr (e : Thir.expression) : expression ESC.t = 
    let lt = e.info in 
    let open IrHir.AstHir in
    match e.exp with 
      | Variable name ->
        let+ id = find_scoped_var name in buildExp lt (Variable id)
      | Literal l -> buildExp lt (Literal l) |> ESC.pure
      | Deref e -> lexpr e 
      | ArrayRead (array_exp,idx) -> let+ arr = rexpr array_exp and* idx' = rexpr idx in buildExp lt (ArrayRead(arr,idx'))
      | UnOp (o, e) -> let+ e' = rexpr e in buildExp lt (UnOp (o, e'))
      | BinOp (o ,e1, e2) ->  let+ e1' = rexpr e1 and* e2' = rexpr e2 in buildExp lt (BinOp(o, e1', e2'))
      | Ref (b, e) -> let+ e' = rexpr e in buildExp lt (Ref(b, e'))
      | ArrayStatic el -> let+ el' = ListM.map rexpr el in buildExp lt (ArrayStatic el')
      | StructRead (struct_exp,field)  -> 
        let+ exp = rexpr struct_exp in 
         buildExp lt (StructRead (exp,field))  
      
      | StructAlloc (id, fields) -> 
        let+ fields = ListM.map (pairMap2 (rexpr)) fields in 
        buildExp lt (StructAlloc(id,fields))
      | MethodCall _ 
      | _ ->  ESC.error @@ Error.make (fst lt) @@ "thir didn't lower correctly this expression" 



      open MonadFunctions(E)
      open MonadSyntax(E)     


  let lower_function decl env (_sm:in_body SailModule.t) : (out_body * SailModule.DeclEnv.t) E.t =
    let _check_function (_,cfg : out_body) : unit E.t = 
      let* ret,unreachable_blocks = cfg_returns cfg in
      if Option.is_some ret && decl.ret <> None then 
        E.log @@ Error.make (Option.get ret) @@ Printf.sprintf "%s doesn't always return !" decl.name
      else
        let () = BlockMap.iter (fun lbl {location=_;_} ->  Logs.debug (fun m -> m "unreachable block %i" lbl)) unreachable_blocks in
        try 
          let _,bb = BlockMap.filter (fun _ {location;_} -> location <> dummy_pos) unreachable_blocks |> BlockMap.choose in
          let _loc = match List.nth_opt bb.assignments 0 with
          | Some v -> v.location
          | None ->  bb.location   in
          E.log @@ Error.make bb.location "unreachable code"
        with Not_found -> E.pure ()
    in
    let check_returns (decls,cfg as res : out_body) : out_body E.t = 
      (* we make sure the last block returns for void methods *)
      let last_bb = BlockMap.find cfg.output cfg.blocks in
      match last_bb.terminator,decl.ret with
      | None,None -> 
        let last_bb = {last_bb with terminator= Some (Return None)} in (* we insert void return *) 
        let blocks = BlockMap.add cfg.output last_bb cfg.blocks in
        (decls,{cfg with blocks}) |> E.pure
      | None,Some _  when  LabelSet.is_empty last_bb.predecessors -> E.throw @@ Error.make decl.pos 
        @@ Printf.sprintf "no return statement but must return %s" 
        @@ string_of_sailtype decl.ret
      | _ -> res |> E.pure
    in

    let rec aux (s : Thir.statement) : out_body ESC.t = 
      let open MonadSyntax(ESC) in 
      let open MonadFunctions(ESC) in 
      let loc = s.info in
      match s.stmt with
      | DeclVar(mut, name, Some ty, None) -> 
        let* bb = emptyBasicBlock loc  in
        let* id = 
          let+ curr_lbl = ESC.get in
          get_scoped_var name (curr_lbl + 1)
        in
        let+ () = ESC.declare_var loc id {ty;mut;name} in
        [{location=loc; mut; id; varType=ty}],bb

      | DeclVar(mut, name, Some ty, Some e) -> 
        let* expression = rexpr e in
        let* id = 
          let+ curr_lbl = ESC.get in
          get_scoped_var name (curr_lbl + 1)
        in
        ESC.declare_var loc id {ty;mut;name} >>
        let target = IrHir.AstHir.buildExp (loc,ty) (Variable id) in
        let+ bn = assignBasicBlock loc {location=loc; target; expression }  in
        [{location=loc; mut; id=id; varType=ty}],bn
        (* ++ other statements *)

      | DeclVar (_,name,None,_) -> failwith @@ "thir broken : variable declaration should have a type : " ^name

      | Skip -> let+ bb = emptyBasicBlock loc in ([],  bb)

      | Assign (e1, e2) -> 
        let* expression = rexpr e2 and* target = lexpr e1 in
        let+ bb = assignBasicBlock loc {location=loc; target; expression} in [],bb
        
      | Seq (s1, s2) ->
        (* let* env = ESC.get_env in *)
        let* d1, cfg1 = aux s1 
        and* d2, cfg2 = aux s2 in
        (* let* () = ESC.set_env env in  *)
        let+ bb = buildSeq cfg1 cfg2 in d1@d2,bb

      | If (e, s, None) -> 
        let* e' = rexpr e in
        let* d, cfg = aux s in
        let+ ite = buildIfThen loc e' cfg in
        (d,ite) 
        
      | If (e, s1, Some s2) -> 
        let* e' = rexpr e in
        let* d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        let+ ite = buildIfThenElse loc e' cfg1 cfg2 in
        (d1@d2, ite) 

      | Loop s ->  
        let* d, cfg = aux s in 
        let+ l = buildLoop loc cfg in
        (d, l)

      | Break -> 
        let* env = ESC.get_env in 
        let bb = {location=loc; env; assignments=[]; predecessors=LabelSet.empty;terminator=Some Break} in
        let+ cfg = singleBlock bb in
        ([],cfg)
        
      | Invoke (target, ({mname;_} as ml), (l,id), el) -> 
        let* (_,realname,_) = ESC.throw_if_none (Error.make loc @@ Fmt.str "Compiler Error : function '%s' must exist" id) 
                                                (SailModule.DeclEnv.find_decl id (Specific (mname,Method)) (snd env))
        in
        let* el' = ListM.map rexpr el in
        let+ invoke = buildInvoke loc {ml with mname} (l,realname) target el' in
        ([], invoke)

      | Return e ->
        let* e = match e with 
        | None -> None |> ESC.pure 
        | Some e -> let+ e' = rexpr e in Some e' in 
        let+ ret =  buildReturn loc e in
        ([], ret)

      | Run _ | Emit _ | Await _ | When _  | Watching _ 
      | Par _  | Case _ | DeclSignal _ -> ESC.error @@ Error.make loc "unimplemented"

      | Block s -> 
        let* env = ESC.get_env in
        let* res = aux s in
        let+ () = ESC.set_env env in
        res

    in 
    Logs.debug (fun m -> m "lowering to MIR %s" decl.name);

    let* (res,_),_env = aux decl.body 0 (fst env) in 
    
    (* some analysis passes *)
    (* let* () = check_function res in *)
    let+ _,cfg as res = check_returns res in

    BlockMap.iter (
      fun l bb -> match bb.terminator with 
      | Some (Return _) -> (* Logs.debug (fun m -> m "found leaf at %i" l); *) reverse_traversal l cfg.blocks |> ignore 
      | _ -> ()
    ) cfg.blocks;
    res,(snd env)

    let preprocess = Error.Logger.pure
  end
)
