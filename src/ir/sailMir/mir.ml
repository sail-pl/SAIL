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
  let declare_var l id v = ES.update (fun e -> VE.declare_var e id (l,v)) |> lift
  let find_var id = bind get_env (fun e -> VE.get_var e id |> pure) 

end

open MonadSyntax(ESC)
open MonadOperator(ESC)
open MonadFunctions(ESC) 


let assign_var (var_l,v:VE.variable) = 
    (var_l,v) |> E.pure


let rename (src : label) (tgt : label) (t : terminator) : terminator = 
  let rn l = if l = src then tgt else l in
  match t with 
    | Goto lbl -> Goto (rn lbl)
    | SwitchInt (st, l, deflt) -> 
      SwitchInt (st, List.map (fun (x, lbl) -> (x, rn lbl)) l, rn deflt)
    | _ -> t

let emptyBasicBlock (location:loc) : cfg ESC.t = 
  let+ lbl = ESC.fresh and* env = ESC.get_env in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl {assignments = []; predecessors = LabelSet.empty; env; location; terminator=None}
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
  let bb = {assignments = [a]; predecessors =  LabelSet.empty; env; location; terminator=None}  in 
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
  | Some Return _ -> cfg1 |> ESC.ok (* if the left block returns, it can't go to the right one *)
  (* todo: handle other cases *)
  | Some _ -> Logs.debug (fun m -> m "MIR : found left terminator with Some");
    {
      input = cfg1.input;
      output = cfg2.output;
      blocks = BlockMap.union assert_disjoint cfg1.blocks cfg2.blocks
    } |> ESC.ok
  | None -> 
    let+ env = ESC.get_env in 
    let bb = {assignments = left.assignments@right.assignments; predecessors = left.predecessors; env; location= right.location; terminator = right.terminator} in
    {
      input = cfg1.input;
      output = if cfg2.input = cfg2.output then cfg1.output else cfg2.output;
      blocks =
        let left = BlockMap.remove cfg1.output cfg1.blocks 
        and right = BlockMap.remove cfg2.input cfg2.blocks |>
                    BlockMap.map (
                      fun bb ->
                         let terminator = MonadOption.M.fmap (rename cfg2.input cfg1.output) bb.terminator 
                         and predecessors =  bb.predecessors |> LabelSet.remove cfg2.input 
                          |> fun pred -> if pred != bb.predecessors then LabelSet.add cfg1.output pred else pred in
                          {bb with predecessors ;terminator}
                    ) 
        in       
        BlockMap.union assert_disjoint left right |> BlockMap.add cfg1.output bb 
     }

let addGoto  (lbl : label) (cfg : cfg) : cfg ESC.t = 
  let* env = ESC.get_env in 
  let bb = {assignments=[]; predecessors=LabelSet.empty; env; location = dummy_pos; terminator=Some (Goto lbl)} in
  let* cfg' = singleBlock bb in 
  buildSeq cfg cfg'


let addPredecessors (lbls : label list) (cfg : cfg) : cfg =
  let open MonadSyntax(MonadOption.M) in
  let blocks = BlockMap.update cfg.input (
    fun bb -> let+ bb in 
    let predecessors = LabelSet.of_list lbls |> LabelSet.union bb.predecessors 
    in {bb with predecessors}
  ) cfg.blocks in
  {cfg with blocks}

let buildIfThen (location : loc) (e : expression) (cfg : cfg) : cfg ESC.t =
  let* outputLbl = ESC.fresh and* inputLbl = ESC.fresh in 
  let* goto = addGoto outputLbl cfg >>| addPredecessors [inputLbl] in
  let+ env = ESC.get_env in 
  let inputBlock = {assignments = []; predecessors = LabelSet.empty ; env; location; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  let outputBlock = {assignments = []; predecessors = LabelSet.of_list [inputLbl;cfg.input] ; env; location = dummy_pos; terminator = None} in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.singleton inputLbl inputBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint goto.blocks
  }


let buildIfThenElse (location : loc) (e : expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg ESC.t = 
  let* inputLbl = ESC.fresh and* outputLbl = ESC.fresh in 
  let* gotoF = addGoto outputLbl cfgFalse >>| addPredecessors [inputLbl]
  and* gotoT = addGoto outputLbl cfgTrue  >>| addPredecessors [inputLbl] in
  
  let+ env = ESC.get_env in 
  let inputBlock = {assignments = [];  predecessors = LabelSet.empty ; env; location; terminator = Some (SwitchInt (e, [(0,cfgFalse.input)], cfgTrue.input))}
  and outputBlock = {assignments = []; env; predecessors = LabelSet.of_list [cfgTrue.output;cfgFalse.output] ; location = dummy_pos; terminator = None} in

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
  let bb1 = {assignments = []; predecessors = LabelSet.empty ; env; location = dummy_pos; terminator = Some (SwitchInt (e, cases, cfg.input))}
  and bb2 = {assignments = []; predecessors = LabelSet.empty ; env; location = dummy_pos; terminator = None} in

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
  let* inputLbl = ESC.fresh and* headLbl = ESC.fresh  and* outputLbl =  ESC.fresh in 
  let inputBlock = {assignments = []; predecessors = LabelSet.empty; env; location; terminator = Some (Goto headLbl)}
  and headBlock = {assignments = []; predecessors = LabelSet.of_list [inputLbl] ; env; location = dummy_pos; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))}
  and outputBlock = {assignments = []; predecessors = LabelSet.of_list [headLbl]; env; location; terminator = None} in
  let+ goto =  addGoto headLbl cfg >>| addPredecessors[headLbl] in
  {
    input = inputLbl;
    output = outputLbl; (* false jumps here *)
    blocks = BlockMap.singleton inputLbl inputBlock  
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.add headLbl headBlock 
              |> BlockMap.union disjoint goto.blocks
  }

let buildInvoke (l : loc) (id : string) (target : string option) (el : expression list) : cfg ESC.t =
  let* env = match target with 
  | None -> ESC.get_env 
  | Some tid -> let* () = ESC.update_var l tid assign_var in ESC.get_env 
  in 
  let+ invokeLbl = ESC.fresh and* returnLbl = ESC.fresh in 
  let invokeBlock = {assignments = []; predecessors = LabelSet.empty ; env; location=l; terminator = Some (Invoke {id = id; target; params = el; next = returnLbl})} in
  let returnBlock = {assignments = []; predecessors = LabelSet.singleton invokeLbl ; env; location = dummy_pos; terminator = None} in 
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.singleton invokeLbl invokeBlock 
              |> BlockMap.add returnLbl returnBlock 
  } 

let buildReturn (location : loc) (e : expression option) : cfg ESC.t =
  let* env = ESC.get_env in 
  let returnBlock = {assignments=[]; predecessors = LabelSet.empty ; env; location; terminator= Some (Return e)} in 
  let+ returnLbl = ESC.fresh in
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }

let get_scoped_var name lbl  =
  if (String.get name 0) = '_' then
    (* already a compiler variable, do not touch it *)
    name
  else
    Printf.sprintf "_%s%i" name lbl

let find_scoped_var name : string ESC.t =
  let rec aux l : string ESC.t = 
    let id = get_scoped_var name l in
    let* v = ESC.find_var id in
    match v with
    | None when l < 0 ->  ESC.pure name (* must be function argument *)
    | None -> aux (l-1)
    | Some _ -> ESC.pure id
  in
  let* curr_lbl = ESC.get in 
  aux (curr_lbl+1)

let rec lexpr (e : Thir.expression) : expression ESC.t = 
  let open IrHir.AstHir in
  match (e:Thir.expression) with 
    | Variable (l,_ as lt, name) ->
      let* id = find_scoped_var name in
      let+ () = ESC.update_var l id assign_var in Variable (lt, id)
    | Deref (_,e) -> rexpr e 
    | ArrayRead (lt, e1, e2) -> let+ e1' = lexpr e1 and* e2' = rexpr e2 in ArrayRead(lt,e1',e2')
    | StructRead _ | StructAlloc _ | EnumAlloc _ | Ref _ -> 
      let l,_ = Thir.extract_exp_loc_ty e in ESC.error [l, "todo"]
    | _ -> failwith "problem with thir"
and rexpr (e : Thir.expression) : expression ESC.t = 
  let open IrHir.AstHir in
  match (e:Thir.expression) with 
    | Variable (lt, name) ->
      let+ id = find_scoped_var name in
      Variable (lt, id)
    | Literal (lt, l) -> Literal (lt, l) |> ESC.pure
    | Deref (_,e) -> lexpr e 
    | ArrayRead (lt,array_exp,idx) -> let+ arr = rexpr array_exp and* idx' = rexpr idx in ArrayRead(lt,arr,idx')
    | StructRead ((l,_),_,_) -> ESC.error [l, "todo"]
    | UnOp (lt, o, e) -> let+ e' = rexpr e in UnOp (lt, o, e')
    | BinOp (lt, o ,e1, e2) ->  let+ e1' = rexpr e1 and* e2' = rexpr e2 in BinOp(lt, o, e1', e2')
    | Ref (lt, b, e) -> let+ e' = rexpr e in Ref(lt, b, e')
    | ArrayStatic (lt, el) -> let+ el' = listMapM rexpr el in ArrayStatic (lt, el')
    | _ -> failwith "problem with thir"


let seqOfList (l : statement list) : statement = 
  List.fold_left (fun s l : statement -> Seq (dummy_pos, s, l)) (Skip dummy_pos) l


let reverse_traversal (lbl:int) (blocks : basicBlock BlockMap.t) :  basicBlock BlockMap.t = 
  let rec aux lbl blocks = 
    let blocks' = BlockMap.remove lbl blocks in
    if blocks' != blocks then
      Logs.debug (fun m -> m "reverse bb %i" lbl);
      match BlockMap.find_opt lbl blocks with
      | None -> blocks'
      | Some bb -> 
          LabelSet.fold (fun lbl b -> aux lbl b) bb.predecessors blocks' 
    in
    aux lbl blocks
    

let cfg_returns ({input;blocks;_} : cfg) : loc option * basicBlock BlockMap.t = 
let rec aux lbl blocks = 
  let blocks' = BlockMap.remove lbl blocks in
  if blocks' != blocks then
    Logs.debug (fun m -> m "checking bb %i" lbl);
    match BlockMap.find_opt lbl blocks with
    | None -> None, blocks'
    | Some bb -> 
      begin
      match bb.terminator with
      | None -> Some bb.location, blocks'
      | Some Return _ -> None, blocks'
      | Some (Invoke {next;_}) -> aux next blocks'
      | Some (Goto lbl) -> aux lbl blocks'
      | Some (SwitchInt (_,cases,default)) -> 
        List.fold_left (fun (_,b) (_,lbl) -> aux lbl b) (aux default blocks') cases
    end
in
aux input blocks

open Pass

module Pass = MakeFunctionPass(V)(
struct
  type in_body = Thir.Pass.out_body
  type out_body = mir_function

  open MonadFunctions(E)
  open MonadSyntax(E) 

  let lower_function decl env : out_body  E.t =
    let check_function (_,cfg : out_body) : unit E.t = 
      let ret,unreachable_blocks = cfg_returns cfg in
      if Option.is_some ret && decl.ret <> None then error [Option.get ret, (Printf.sprintf "%s doesn't always return !" decl.name)]
      else
        let () = BlockMap.iter (fun lbl {location=_;_} ->  Logs.debug (fun m -> m "unreachable block %i" lbl)) unreachable_blocks in
        try 
          let _,bb = BlockMap.filter (fun _ {location;_} -> location <> dummy_pos) unreachable_blocks |> BlockMap.choose in
          let _loc = match List.nth_opt bb.assignments 0 with
          | Some v -> v.location
          | None ->  bb.location   in
          error [bb.location, "unreachable code"] 
        with Not_found -> ok ()
    in
    let check_returns (decls,cfg as res : out_body) : out_body E.t = 
      (* we make sure the last block returns for void methods *)
      let last_bb = BlockMap.find cfg.output cfg.blocks in
      match last_bb.terminator with
      | None when decl.ret = None -> 
        let last_bb = {last_bb with terminator= Some (Return None)} in (* we insert void return *) 
        let blocks = BlockMap.add cfg.output last_bb cfg.blocks in
        ok (decls,{cfg with blocks})
      | _ -> ok res
    in

    let rec aux (s : Thir.statement) : out_body ESC.t = 
      let open MonadSyntax(ESC) in 
      let open MonadFunctions(ESC) in 
      match s with
      | DeclVar(loc, mut, name, Some ty, None) -> 
        let* bb = emptyBasicBlock loc  in
        let* id = 
          let+ curr_lbl = ESC.get in
          get_scoped_var name (curr_lbl + 1)
        in
        let+ () = ESC.declare_var loc id {ty;mut;name} in
        [{location=loc; mut; id; varType=ty}],bb

      | DeclVar(loc, mut, name, Some ty, Some e) -> 
        let* expression = rexpr e in
        let* id = 
          let+ curr_lbl = ESC.get in
          get_scoped_var name (curr_lbl + 1)
        in
        let* () = ESC.declare_var loc id {ty;mut;name} in
        let+ bn = assignBasicBlock loc {location=loc; target=Variable ((loc, ty), id); expression }  in
        [{location=loc; mut; id=id; varType=ty}],bn
        (* ++ other statements *)

      | DeclVar _ as s -> ESC.error [Thir.extract_statements_loc s, "Declaration should have type "]  (* -> add generic parameter to statements *)

      | Skip loc -> let+ bb = emptyBasicBlock loc in ([],  bb)

      | Assign (loc, e1, e2) -> 
        let* expression = rexpr e2 and* target = lexpr e1 in
        let+ bb = assignBasicBlock loc {location=loc; target; expression} in [],bb
        
      | Seq (_, s1, s2) ->
        (* let* env = ESC.get_env in *)
        let* d1, cfg1 = aux s1 
        and* d2, cfg2 = aux s2 in
        (* let* () = ESC.set_env env in  *)
        let+ bb = buildSeq cfg1 cfg2 in d1@d2,bb

      | If (loc, e, s, None) -> 
        let* e' = rexpr e in
        let* d, cfg = aux s in
        let+ ite = buildIfThen loc e' cfg in
        (d,ite) 
        
      | If (loc, e, s1, Some s2) -> 
        let* e' = rexpr e in
        let* d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        let+ ite = buildIfThenElse loc e' cfg1 cfg2 in
        (d1@d2, ite) 

      | While (loc, e, s) ->  
        let* e' = rexpr e in
        let* d, cfg = aux s in 
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

      | Block (_l, s) -> 
        let* env = ESC.get_env in
        let* res = aux s in
        let+ () = ESC.set_env env in
        res

    in 
    Logs.debug (fun m -> m "lowering to MIR %s" decl.name);

    let* (res,_),_env = aux decl.body 0 (fst env) in

    (* some analysis passes *)
    let* () = check_function res in
    let+ _,cfg as res = check_returns res in

    BlockMap.iter (
      fun l bb -> match bb.terminator with 
      | Some (Return _) -> Logs.debug (fun m -> m "found leaf at %i" l); reverse_traversal l cfg.blocks |> ignore 
      | _ -> ()
    ) cfg.blocks;
    res

  end
)
