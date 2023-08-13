open AstMir
open Common 
open TypesCommon
open Monad
open MirMonad
open UseMonad(M)
let assign_var (var_l,v:VE.variable) = 
  (var_l,v) |> M.E.pure

let rename (src : label) (tgt : label) (t : terminator) : terminator = 
  let rn l = if l = src then tgt else l in
  match t with 
    | Goto lbl -> Goto (rn lbl)
    | SwitchInt si -> 
      SwitchInt  {choice=si.choice ; paths=List.map (fun (x, lbl) -> (x, rn lbl)) si.paths; default=rn si.default}
    | _ -> t

let emptyBasicBlock (location:loc) : cfg M.t = 
  let+ lbl = M.fresh_block and* env = M.get_env in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl {assignments = []; predecessors = LabelSet.empty; forward_info=env; backward_info = (); location; terminator=None}
  }

let singleBlock (bb : _ basicBlock) : cfg M.t = 
  let+ lbl = M.fresh_block in    
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }

let assignBasicBlock (location : loc) (a : assignment) : cfg M.t = 
  let* env = M.get_env in
  let bb = {assignments = [a]; predecessors =  LabelSet.empty; forward_info=env; backward_info = (); location; terminator=None}  in 
  let+ lbl = M.fresh_block in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }


let disjoint = (fun _ _ _ -> None) 
let assert_disjoint = (fun _ _ _ -> failwith "illegal label sharing")


let buildSeq (cfg1 : cfg) (cfg2 : cfg) : cfg M.t = 
  let left =  BlockMap.find cfg1.output cfg1.blocks 
  and right = BlockMap.find cfg2.input cfg2.blocks 
  in 
  match left.terminator with 
  | Some (Invoke _) -> let+ () = M.error @@ Error.make left.location "invalid output node" in cfg1
  | Some _ ->
    {
      input = cfg1.input;
      output = cfg2.output;
      blocks = BlockMap.union assert_disjoint cfg1.blocks cfg2.blocks
    } |> M.ok
  | None -> 
    let+ env = M.get_env in 
    let bb = {assignments = left.assignments@right.assignments; predecessors = left.predecessors; forward_info=env; backward_info = (); location= right.location; terminator = right.terminator} in
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

let addGoto  (lbl : label) (cfg : cfg) : cfg M.t = 
  let* env = M.get_env in 
  let bb = {assignments=[]; predecessors=LabelSet.empty; forward_info=env; backward_info = (); location = dummy_pos; terminator=Some (Goto lbl)} in
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

let buildIfThen (location : loc) (e : expression) (cfg : cfg) : cfg M.t =
  let* outputLbl = M.fresh_block and* inputLbl = M.fresh_block in 
  let* goto = addGoto outputLbl cfg >>| addPredecessors [inputLbl] in
  let+ env = M.get_env in 
  let inputBlock = {assignments = []; predecessors = LabelSet.empty ; forward_info=env; backward_info = (); location; terminator = Some (SwitchInt {choice=e; paths=[(0,outputLbl)]; default=cfg.input})} in
  let outputBlock = {assignments = []; predecessors = LabelSet.of_list [inputLbl;cfg.input] ; forward_info=env; backward_info = (); location; terminator = None} in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.(singleton inputLbl inputBlock 
              |> add outputLbl outputBlock 
              |> union disjoint goto.blocks)
  }


let buildIfThenElse (location : loc) (e : expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg M.t = 
  let* inputLbl = M.fresh_block and* outputLbl = M.fresh_block in 
  let* gotoF = addGoto outputLbl cfgFalse >>| addPredecessors [inputLbl]
  and* gotoT = addGoto outputLbl cfgTrue  >>| addPredecessors [inputLbl] in
  
  let+ env = M.get_env in 
  let inputBlock = {assignments = [];  predecessors = LabelSet.empty ; forward_info=env; backward_info = (); location; terminator = Some (SwitchInt {choice=e; paths=[(0,cfgFalse.input)]; default=cfgTrue.input})}
  and outputBlock = {assignments = []; forward_info=env; backward_info = (); predecessors = LabelSet.of_list [cfgTrue.output;cfgFalse.output] ; location; terminator = None} in

  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.(singleton inputLbl inputBlock 
              |> add outputLbl outputBlock 
              |> union disjoint gotoT.blocks
              |> union disjoint gotoF.blocks)
  }


let buildSwitch (choice : expression) (blocks : (int * cfg) list) (cfg : cfg): cfg M.t = 
  let* env = M.get_env in 
  let paths = List.map (fun (value, cfg) -> (value, cfg.input)) blocks in 
  let bb1 = {assignments = []; predecessors = LabelSet.empty ; forward_info=env; backward_info = (); location = dummy_pos; terminator = Some (SwitchInt {choice ; paths; default=cfg.input})}
  and bb2 = {assignments = []; predecessors = LabelSet.empty ; forward_info=env; backward_info = (); location = dummy_pos; terminator = None} in

  let* input =  M.fresh_block and* output = M.fresh_block in 
  let+ gotos = ListM.map (fun (_,cfg) -> addGoto output cfg) blocks in 
  {
    input = input;
    output = output;
    blocks = BlockMap.(singleton input bb1  
              |> add output bb2 
              |> List.fold_left (fun r bb -> BlockMap.union disjoint bb.blocks r)
            ) gotos  
  }

let buildLoop (location : loc) (cfg : cfg) : cfg M.t = 
  let* env =  M.get_env in 
  let* inputLbl = M.fresh_block and* outputLbl = M.fresh_block in 
  
  (* all break terminators within the body go to outputLbl *)
  let bm1,bm2 = BlockMap.partition (fun _ {terminator;_} -> terminator = Some Break) cfg.blocks in
  let preds,bm1 = BlockMap.fold (fun l bb (lbls,bbs) -> l::lbls,BlockMap.add l {bb with terminator = Some (Goto outputLbl)} bbs ) bm1 ([],BlockMap.empty) in 

  let inputBlock = {assignments = []; predecessors = LabelSet.empty; forward_info=env; backward_info = (); location; terminator = Some (Goto cfg.input)} in
  let outputBlock = {assignments = []; predecessors = LabelSet.of_list preds; forward_info=env; backward_info = (); location; terminator = None} in
  let cfg =  {cfg with blocks=BlockMap.union assert_disjoint bm1 bm2} in 

  (* make the loop *)
  let+ goto = addGoto cfg.input cfg >>| addPredecessors [cfg.input] in

  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.(singleton inputLbl inputBlock |> add outputLbl outputBlock |> union disjoint goto.blocks)
  }

let buildInvoke (l : loc) (origin:l_str) (id : l_str) (target : string option) (el : expression list) : cfg M.t =
  let* env = match target with 
  | None -> M.get_env 
  | Some tid -> M.update_var l tid assign_var >>= fun () -> M.get_env
  in 
  let+ invokeLbl = M.fresh_block and* returnLbl = M.fresh_block in 
  let invokeBlock = 
  {
      assignments = []; 
      predecessors = LabelSet.empty ; 
      forward_info = env;
      backward_info = (); 
      location=l; 
      terminator = Some (Invoke {id = (snd id); origin; target; params = el; next = returnLbl})
  } in
  let returnBlock = {assignments = []; predecessors = LabelSet.singleton invokeLbl ; forward_info = env; backward_info = () ; location = dummy_pos; terminator = None} in 
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.(singleton invokeLbl invokeBlock |> add returnLbl returnBlock)
  } 

let buildReturn (location : loc) (e : expression option) : cfg M.t =

  let* env = M.get_env in 
  let returnBlock = {assignments=[]; predecessors = LabelSet.empty ; forward_info=env; backward_info = (); location; terminator= Some (Return e)} in 
  let+ returnLbl = M.fresh_block in
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }

let get_scoped_var name lbl  =
  if String.get name 0 = '_' then
    (* already a compiler variable, do not touch it *)
    name
  else
    Printf.sprintf "_%s%i" name lbl

let find_scoped_var name : string M.t =
  let rec aux l : string M.t = 
    let id = get_scoped_var name l in
    let* v = M.find_var id in
    match v with
    | None when l < 0 ->  M.pure name (* must be function argument *)
    | None -> aux (l-1)
    | Some _ -> M.pure id
  in
  let* v = M.current_scoped_var in 
  aux v


let seqOfList (l : statement list) : statement = 
  List.fold_left (fun s l : statement ->  {info=dummy_pos; stmt=Seq (s, l)}) {info=dummy_pos;stmt=Skip} l



module Traversal(M : Monad) = struct
  open UseMonad(M)
  (* let backward (lbl:int) (blocks : _ basicBlock BlockMap.t) :  _ basicBlock BlockMap.t M.t = 
  let rec aux lbl blocks = 
    let blocks' = BlockMap.remove lbl blocks in
    match BlockMap.find_opt lbl blocks with
    | None -> blocks'
    | Some bb -> LabelSet.fold aux bb.predecessors blocks' 
    in
    aux lbl blocks *)


  let forward (lbl:int) (type a) (blocks : (a,'b) basicBlock BlockMap.t) (f : (a,'b) basicBlock -> ('c,'d) basicBlock M.t) : ('c,'d) basicBlock BlockMap.t M.t= 
  let rec aux lbl blocks : (int * ('c, 'd) basicBlock) Seq.t M.t = 
    match BlockMap.find_opt lbl blocks with
    Some b -> 
      let* b = f b in
      let blocks = BlockMap.remove lbl blocks in 
      let s = Seq.return (lbl,b) in 
      begin
      match b.terminator with
      | None -> M.pure s
      | Some (Goto l) -> let+ s' = aux l blocks in Seq.append s s'
      | Some (SwitchInt si) -> 
        let* default = aux si.default blocks <&> Seq.append s in
        ListM.fold_left (fun seq (_,lbl) -> aux lbl blocks <&> Seq.append seq) default si.paths
      | Some (Invoke i) -> let+ s' = aux i.next blocks in Seq.append s s'
      | _ -> M.pure s
      end
    | None -> M.pure Seq.empty
  
  in
  let+ res = aux lbl blocks in BlockMap.of_seq res
end



