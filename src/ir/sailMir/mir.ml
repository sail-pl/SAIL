open AstMir
open IrThir
open Common 
open TypesCommon
open Result
open Monad


module E = Error.MonadError
module ES = MonadState.T(E)(VE)
module ESC = struct 
  include MonadState.CounterTransformer(ES)
  let error e = error e |> ES.lift |> lift
  let ok e = ok e |> ES.lift |> lift
  let get_env = ES.get |> lift    
  let update_env f = ES.update f |> lift
  let set_env e = ES.set e |> lift
  let update_var l f id = ES.update (fun e -> VE.update_var e l id f ) |> lift

end

open MonadSyntax(ESC)
open MonadFunctions(ESC) 


let assign_var l (var_l,v:VE.variable) = 
  if (not v.mut) && v.is_init then
    error [l, "can't assign twice to immutable variable"]
  else 
    (var_l,{v with is_init=true}) |> E.pure


let rename (src : label) (tgt : label) (t : terminator) : terminator = 
  match t with 
    | Goto lbl when lbl = src -> Goto tgt 
    | SwitchInt (st, l, deflt) -> 
      SwitchInt (st, List.map (fun (x, lbl) -> (x, if lbl = src then tgt else lbl)) l, 
        if src = deflt then tgt else deflt)
    | _ -> t

let emptyBasicBlock (location:loc) : cfg ESC.t = 
  let+ lbl = ESC.fresh and* env = ESC.get_env in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl {assignments = []; env; location; terminator=None}
  }

let singleBlock (bb : basicBlock) : cfg ESC.t = 
  let+ lbl = ESC.fresh in    
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }

let assignBasicBlock (location : loc) (a : assignment) : cfg ESC.t = 
  let* env = ESC.get_env in
  let bb = {assignments = [a]; env; location; terminator=None}  in 
  let+ lbl = ESC.fresh in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }


let disjoint = (fun _ _ _ -> None) 
let assert_disjoint = (fun _ _ _ -> failwith "illegal label sharing")


let buildSeq (cfg1 : cfg) (cfg2 : cfg) : cfg ESC.t = 
  let left =  BlockMap.find cfg1.output cfg1.blocks 
  and right = BlockMap.find cfg2.input cfg2.blocks 
  in 
  match left.terminator with 
  | Some (Invoke _) -> ESC.error [left.location, "invalid output node"]
  (* todo: handle other cases *)
  | Some _ -> 
    {
      input = cfg1.input;
      output = cfg2.output;
      blocks = BlockMap.union assert_disjoint cfg1.blocks cfg2.blocks
    } |> ESC.ok
  | None -> 
    let+ env = ESC.get_env in 
    let bb = {assignments = left.assignments@right.assignments; env; location= right.location; terminator = right.terminator} in
    {
      input = cfg1.input;
      output = if cfg2.input = cfg2.output then cfg1.output else cfg2.output;
      blocks =
        let left = BlockMap.remove cfg1.output cfg1.blocks in 
        let right = BlockMap.remove cfg2.input cfg2.blocks |>
                    BlockMap.map 
                      (fun bb -> 
                        let terminator = MonadOption.M.fmap (rename cfg2.input cfg1.output) bb.terminator in
                        {bb with terminator}) 
        in       
        BlockMap.union assert_disjoint left right |> BlockMap.add cfg1.output bb 
     }

let addGoto  (lbl : label) (cfg : cfg) : cfg ESC.t = 
  let* env = ESC.get_env in 
  let bb = {assignments=[]; env; location = dummy_pos; terminator=Some (Goto lbl)} in
  let* cfg' = singleBlock bb in 
  buildSeq cfg cfg'


let buildIfThen (location : loc) (e : expression) (cfg : cfg) : cfg ESC.t =
  let* env = ESC.get_env in 
  let outputBlock = {assignments = []; env; location = dummy_pos; terminator = None} in
  let* outputLbl = ESC.fresh and* inputLbl = ESC.fresh in 
  let+ goto = addGoto outputLbl cfg in
  let inputBlock = {assignments = []; env; location; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.singleton inputLbl inputBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint goto.blocks
  }


let buildIfThenElse (location : loc) (e : expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg ESC.t = 
  let* env = ESC.get_env in 
  let outputBlock = {assignments = []; env; location = dummy_pos; terminator = None}
  and inputBlock = {assignments = []; env; location; terminator = Some (SwitchInt (e, [(0,cfgFalse.input)], cfgTrue.input))} in
  
  let* inputLbl = ESC.fresh and* outputLbl = ESC.fresh in 
  let+ gotoF = addGoto outputLbl cfgFalse and* gotoT = addGoto outputLbl cfgTrue in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.singleton inputLbl inputBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint gotoT.blocks
              |> BlockMap.union disjoint gotoF.blocks
  }


let buildSwitch (e : expression) (blocks : (int * cfg) list) (cfg : cfg): cfg ESC.t = 
  let* env = ESC.get_env in 
  let cases = List.map (fun (value, cfg) -> (value, cfg.input)) blocks in 
  let bb1 = {assignments = []; env; location = dummy_pos; terminator = Some (SwitchInt (e, cases, cfg.input))}
  and bb2 = {assignments = []; env; location = dummy_pos; terminator = None} in

  let* input =  ESC.fresh and* output = ESC.fresh in 
  let+ gotos = listMapM (fun (_,cfg) -> addGoto output cfg) blocks in 
  {
    input = input;
    output = output;
    blocks = ( BlockMap.singleton input bb1 
                |> BlockMap.add output bb2  
                |> List.fold_left (fun r bb -> BlockMap.union disjoint bb.blocks r)
              ) gotos  
  }

let buildLoop (location : loc) (e : expression) (cfg : cfg) : cfg ESC.t = 
  let* env =  ESC.get_env in 
  let outputBlock = {assignments = []; env; location; terminator = None} in
  let* inputLbl =  ESC.fresh and* headLbl = ESC.fresh and* outputLbl =  ESC.fresh in 
  let+ goto = addGoto inputLbl cfg in
  let headBlock = {assignments = []; env; location = dummy_pos; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  {
    input = headLbl;
    output = outputLbl; (* false jumps here *)
    blocks = BlockMap.singleton inputLbl headBlock 
              |> BlockMap.add headLbl headBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint goto.blocks
  }

let buildInvoke (l : loc) (id : string) (target : string option) (el : expression list) : cfg ESC.t =
  let* env = match target with 
  | None -> ESC.get_env 
  | Some tid -> let* () = ESC.update_var l tid (assign_var l) in ESC.get_env 
  in 
  let returnBlock = {assignments = []; env; location = dummy_pos; terminator = None} in 
  let+ invokeLbl = ESC.fresh and* returnLbl = ESC.fresh in 
  let invokeBlock = {assignments = []; env; location=l; terminator = Some (Invoke {id = id; target; params = el; next = returnLbl})} in
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.singleton invokeLbl invokeBlock 
              |> BlockMap.add returnLbl returnBlock 
  } 

let buildReturn (location : loc) (e : expression option) : cfg ESC.t =
  let* env = ESC.get_env in 
  let returnBlock = {assignments=[]; env; location; terminator= Some (Return e)} in 
  let+ returnLbl = ESC.fresh in
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }


let rec lexpr (e : Thir.expression) : expression ESC.t = 
  let open IrHir.AstHir in
  match (e:Thir.expression) with 
    | Variable (l,_ as lt, id) ->
      let+ () = ESC.update_var l id (assign_var l) in Variable (lt, id)
    | Deref (_,e) -> rexpr e 
    | ArrayRead (lt, e1, e2) -> let+ e1' = lexpr e1 and* e2' = rexpr e2 in ArrayRead(lt,e1',e2')
    | StructRead _ | StructAlloc _ | EnumAlloc _ | Ref _ -> 
      let l,_ = Thir.extract_exp_loc_ty e in ESC.error [l, "todo"]
    | _ -> failwith "problem with thir"
and rexpr (e : Thir.expression) : expression ESC.t = 
let open IrHir.AstHir in
  match (e:Thir.expression) with 
    | Variable (l,_ as lt, id) ->
      let upd (old_l,v) = 
        if v.is_init then (old_l,{v with is_used=true}) |> E.pure 
        else error [l,Printf.sprintf "%s uninitialized value" id]
      in
      let+ () = ESC.update_var l id upd in Variable (lt, id)
    | Literal (lt, l) -> Literal (lt, l) |> ESC.pure
    | Deref (_,e) -> lexpr e 
    | ArrayRead (_,ent,_) | StructRead (_,ent,_) -> 
      (* array and struct are used if we access one of their elements *)
      let* _ = rexpr ent in lexpr e
    | UnOp (lt, o, e) -> let+ e' = rexpr e in UnOp (lt, o, e')
    | BinOp (lt, o ,e1, e2) ->  let+ e1' = rexpr e1 and* e2' = rexpr e2 in BinOp(lt, o, e1', e2')
    | Ref (lt, b, e) -> let+ e' = rexpr e in Ref(lt, b, e')
    | ArrayStatic (lt, el) -> let+ el' = listMapM rexpr el in ArrayStatic (lt, el')
  | _ -> failwith "problem with thir"


let seqOfList (l : statement list) : statement = 
  List.fold_left (fun s l : statement -> Seq (dummy_pos, s, l)) (Skip dummy_pos) l


let cfg_returns ({input;blocks;_} : cfg) : loc option * basicBlock BlockMap.t = 
  let rec aux lbl blocks = 
    Logs.debug (fun m -> m "checking bb %i" lbl);
  let blocks' = BlockMap.remove lbl blocks in
  match BlockMap.find_opt lbl blocks with
  | None -> Logs.debug (fun m -> m "loop detected for bb %i" lbl); None, blocks'
  | Some bb -> 
    begin
    match bb.terminator with
    | None -> Some bb.location, blocks'
    | Some Return _ -> None, blocks'
    | Some (Invoke {next;_}) -> aux next blocks'
    | Some (Goto lbl) -> aux lbl blocks'
    | Some (SwitchInt (_,cases,default)) -> List.fold_left (fun (ret,b) (_,lbl) -> if Option.is_none ret then aux lbl b else ret,b) (aux default blocks') cases
  end
  in
  aux input blocks
  

open Pass

module Pass = MakeFunctionPass(V)(
struct
  type in_body = Thir.Pass.out_body
  type out_body = declaration list * cfg


  open MonadSyntax(ESC)

  let lower_function decl env : out_body  E.t =
    let rec aux : Thir.statement -> (declaration list * cfg) ESC.t = function
      | DeclVar(loc, mut, id, Some ty, None) -> 
        let* () = ESC.update_env (fun e -> VE.declare_var e id (loc,{ty;mut;is_init=false;is_used=false})) in
        let+ bb = emptyBasicBlock loc  in
        [{location=loc; mut; id; varType=ty}],bb

      | DeclVar(loc, mut, id, Some ty, Some e) -> 
        let* () = ESC.update_env (fun e -> VE.declare_var e id (loc,{ty;mut;is_init=true;is_used=false})) in
        let* expression = rexpr e in
        let+ bn = assignBasicBlock loc ({location=loc; target=Variable ((loc, ty), id); expression })  in
        [{location=loc; mut; id=id; varType=ty}],bn
        (* ++ other statements *)

      | DeclVar _ as s -> ESC.error [Thir.extract_statements_loc s, "Declaration should have type "]  (* -> add generic parameter to statements *)

      | Skip loc -> let+ bb = emptyBasicBlock loc in ([],  bb)

      | Assign (loc, e1, e2) -> 
        let* target = lexpr e1 and* expression = rexpr e2 in
        let+ bb = assignBasicBlock loc ({location=loc; target; expression}) in [],bb
        
      | Seq (_, s1, s2) ->
        (* let* env = ESC.get_env in *)
        let* d1, cfg1 = aux s1 
        and* d2, cfg2 = aux s2 in
        (* let* () = ESC.set_env env in  *)
        let+ bb = buildSeq cfg1 cfg2 in d1@d2,bb

      | If (loc, e, s, None) -> 
        let* d, cfg = aux s in
        let* e' = rexpr e in
        let+ ite = buildIfThen loc e' cfg in
        (d,ite) 
        
      | If (loc, e, s1, Some s2) -> 
        let* d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        let* e' = rexpr e in
        let+ ite = buildIfThenElse loc e' cfg1 cfg2 in
        (d1@d2, ite) 

      | While (loc, e, s) ->  
        let* d, cfg = aux s in 
        let* e' = rexpr e in
        let+ l = buildLoop loc e' cfg in
        (d, l)
        
      | Invoke (loc, target, id, el) -> 
        let* el' = listMapM rexpr el in
        let+ invoke = buildInvoke loc id target el' in
        ([], invoke)

      | Return (loc, e) ->
        let* e = match e with 
        | None -> None |> ESC.pure 
        | Some e -> let+ e' = rexpr e in Some e' in 
        let+ ret =  buildReturn loc e in
        ([], ret)

      | Run _ | Emit _ | Await _ | When _  | Watching _ 
      | Par _  | Case _ | DeclSignal _ as s -> ESC.error [Thir.extract_statements_loc s, "unimplemented"]

      | Block (location, s) -> 
          let* () = ESC.update_env (fun e -> VE.new_frame e |> E.pure) in
          let* decls,cfg = aux s in

          let pop (e:VE.t) : VE.t E.t = 
            let open MonadSyntax(E) in
            let open MonadFunctions(E) in
            let current,env = VE.current_frame e in
            let+ () = mapIterM (
              fun id (_l,v) -> if not v.is_used then
                let () = Logs.warn (fun m -> m "unused variable %s" id) in
                () |> E.pure
                (* error [l, "unused variable"]  todo: add warnings *)
              else
                () |> E.pure
            ) current in
            env
          in
          let* () = ESC.update_env pop in

          let* env = ESC.get_env in 

          let bb = {assignments=[]; env; location; terminator=Some (Goto cfg.input)} in
          let* () = ESC.set_env env in
          let* cfg' = singleBlock bb in 
          let cfg' = 
          {
            input = cfg'.input;
            output = cfg.output;
            blocks = BlockMap.union assert_disjoint cfg'.blocks cfg.blocks
          } in
          (decls,cfg') |> ESC.pure
            
    in 

    Logs.debug (fun m -> m "lowering to MIR %s" decl.name);
    let open MonadSyntax(E) in
    let* ((decls,cfg) as res,_),_ = aux decl.body 0 (fst env)  in
    
    let ret,unreachable_blocks = cfg_returns cfg in
    if Option.is_some ret && decl.ret <> None then error [Option.get ret, (Printf.sprintf "%s doesn't always return !" decl.name)]
    else
      let () = BlockMap.iter (fun lbl {location=_;_} ->  Logs.debug (fun m -> m "unreachable block %i" lbl)) unreachable_blocks in
      let* () =
      try 
        let _,bb = BlockMap.filter (fun _ {location;_} -> location <> dummy_pos) unreachable_blocks |> BlockMap.choose in
        let _loc = match List.nth_opt bb.assignments 0 with
        | Some v -> v.location
        | None ->  bb.location   in
        error [bb.location, "unreachable code"] 
      with Not_found -> ok ()
      in
    (* we make sure the last block returns for void methods *)
      let last_bb = BlockMap.find cfg.output cfg.blocks in
      match last_bb.terminator with
      | None when decl.ret = None -> 
        let last_bb = {last_bb with terminator= Some (Return None)}  (* we insert void return *) in
        let blocks = BlockMap.add cfg.output last_bb cfg.blocks in
        ok (decls,{cfg with blocks})
      | _ -> ok res
  end
)
