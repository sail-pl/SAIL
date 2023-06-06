open AstMir
open Common 
open TypesCommon
open Monad
open MirMonad

open MonadSyntax(ESC)
open MonadFunctions(ESC)
open MonadOperator(ESC)


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
  | Some (Invoke _) -> let+ () = ESC.error @@ Error.make left.location "invalid output node" in cfg1
  | Some _ ->
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
  let outputBlock = {assignments = []; predecessors = LabelSet.of_list [inputLbl;cfg.input] ; env; location; terminator = None} in
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
  and outputBlock = {assignments = []; env; predecessors = LabelSet.of_list [cfgTrue.output;cfgFalse.output] ; location; terminator = None} in

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
  let+ gotos = ListM.map (fun (_,cfg) -> addGoto output cfg) blocks in 
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
  and headBlock = {assignments = []; predecessors = LabelSet.of_list [inputLbl] ; env; location; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in

  let bm1,bm2 = BlockMap.partition (fun _ {terminator;_} -> terminator = Some Break) cfg.blocks in
  let preds,bm1 = BlockMap.fold (fun l bb (lbls,bbs) -> l::lbls,BlockMap.add l {bb with terminator = Some (Goto outputLbl)} bbs ) bm1 ([],BlockMap.empty) in 

  let outputBlock = {assignments = []; predecessors = LabelSet.of_list (headLbl::preds); env; location; terminator = None} in
  let cfg =  {cfg with blocks=BlockMap.union assert_disjoint bm1 bm2} in 


  let+ goto =  addGoto headLbl cfg >>| addPredecessors [headLbl] in
  {
    input = inputLbl;
    output = outputLbl; (* false jumps here *)
    blocks = BlockMap.singleton inputLbl inputBlock  
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.add headLbl headBlock 
              |> BlockMap.union disjoint goto.blocks
  }

let buildInvoke (l : loc) (origin:import) (id : loc * string) (target : string option) (el : expression list) : cfg ESC.t =
  let* env = match target with 
  | None -> ESC.get_env 
  | Some tid -> ESC.update_var l tid assign_var >> ESC.get_env 
  in 
  let+ invokeLbl = ESC.fresh and* returnLbl = ESC.fresh in 
  let invokeBlock = 
  {
      assignments = []; 
      predecessors = LabelSet.empty ; env; 
      location=l; 
      terminator = Some (Invoke {id = (snd id); origin; target; params = el; next = returnLbl})
  } in
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


let seqOfList (l : statement list) : statement = 
  List.fold_left (fun s l : statement ->  {info=dummy_pos; stmt=Seq (s, l)}) {info=dummy_pos;stmt=Skip} l


let reverse_traversal (lbl:int) (blocks : basicBlock BlockMap.t) :  basicBlock BlockMap.t = 
  let rec aux lbl blocks = 
    let blocks' = BlockMap.remove lbl blocks in
    
    (* if blocks' != blocks then
      Logs.debug (fun m -> m "reverse bb %i" lbl); *)

    match BlockMap.find_opt lbl blocks with
    | None -> blocks'
    | Some bb -> 
        LabelSet.fold (fun lbl b -> aux lbl b) bb.predecessors blocks' 
    in
    aux lbl blocks
    

let cfg_returns ({input;blocks;_} : cfg) : (loc option * basicBlock BlockMap.t) E.t = 
  let open MonadFunctions(E) in 
  let open MonadSyntax(E) in 
  let open MonadOperator(E) in
  let rec aux lbl blocks = 
    let blocks' = BlockMap.remove lbl blocks in

    (* 
    if blocks' != blocks then
      Logs.debug (fun m -> m "checking bb %i" lbl);
    *) 
    
    match BlockMap.find_opt lbl blocks with
    | None -> (None, blocks') |> E.pure
    | Some bb -> 
      begin
      match bb.terminator with
      | None -> (Some bb.location, blocks') |> E.pure
      | Some Break -> E.log @@ Error.make bb.location "there should be no break at this point" >> aux input blocks'
      | Some Return _ -> (None, blocks') |> E.pure
      | Some (Invoke {next;_}) -> aux next blocks'
      | Some (Goto lbl) -> aux lbl blocks'
      | Some (SwitchInt (_,cases,default)) -> 

        let* x = aux default blocks' in 
        ListM.fold_left (fun (_,b) (_,lbl) -> aux lbl b) x cases
    end
  in
aux input blocks