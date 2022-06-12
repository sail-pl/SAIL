open AstMir
open IrHir
open IrThir
open Common 

let label_cpt = ref 0

let fresh_label () = 
  let fresh = !label_cpt in 
  let _ = incr label_cpt in fresh

let rename (src : label) (tgt : label) (t : terminator) : terminator = 
  match t with 
    | Goto lbl when lbl = src -> Goto tgt 
    | Invoke {id ; params ; next} -> Invoke {id ; params; next}
    | SwitchInt (st, l, deflt) -> 
      SwitchInt (st, List.map (fun (x, lbl) -> (x, if lbl = src then tgt else lbl)) l, 
        if src = deflt then tgt else deflt)
    | _ -> t

let singleBlock (bb : basicBlock) : cfg = 
  let lbl = fresh_label () in
    {
      input = lbl;
      output = lbl;
      blocks = BlockMap.singleton lbl bb
    }

let buildSingle (sl : statement list) = 
  let bb = {statements = sl; terminator = None} in 
  singleBlock bb

exception InvalidOutputNode

let buildSeq (cfg1 : cfg) (cfg2 : cfg) : cfg = 
  let left = BlockMap.find cfg1.output cfg1.blocks in 
  let right = BlockMap.find cfg2.input cfg2.blocks in
  match left.terminator with 
  | None -> 
    let bb = {statements = left.statements@right.statements; terminator = right.terminator} in
    {
      input = cfg1.input;
      output = if cfg1.input = cfg2.output then cfg1.output else cfg2.output;
      blocks =
        let left = BlockMap.remove cfg1.output cfg1.blocks in 
        let right = BlockMap.map 
                      (fun {statements; terminator} -> 
                        {statements; terminator = Option.MonadOption.fmap (rename cfg2.input cfg1.output) terminator}) 
                      (BlockMap.remove cfg2.input cfg2.blocks) in       
        let right =  BlockMap.add cfg1.output bb (BlockMap.union (fun _ _ _ -> None) left right)
      in BlockMap.union (fun _ _ _ -> None) cfg1.blocks right 
    }
  | Some (Invoke _) -> raise InvalidOutputNode (* Handle other cases*)
  | Some _ -> 
    {
      input = cfg1.input;
      output = cfg2.output;
      blocks = BlockMap.union (fun _ _ _ -> None) cfg1.blocks cfg2.blocks
    }


let addGoto (lbl : label) (cfg : cfg) : cfg = 
  let bb = {statements=[]; terminator=Some (Goto lbl)} in
  let cfg' = singleBlock bb in 
  buildSeq cfg cfg' 

  let buildIfThen (e : AstThir.expression) (cfg : cfg) : cfg = 
    let outputLbl = fresh_label () in
    let outputBlock = {statements = []; terminator = None} in
    let inputLbl = fresh_label () in 
    let inputBlock = {statements = []; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
    {
      input = inputLbl;
      output = outputLbl;
      blocks = 
        BlockMap.union (fun _ _ _ -> None) ((addGoto outputLbl cfg).blocks )
        (BlockMap.add outputLbl outputBlock (BlockMap.singleton inputLbl inputBlock))
    }

let buildIfThenElse (e : AstThir.expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg = 
  let outputLbl = fresh_label () in
  let outputBlock = {statements = []; terminator = None} in
  let inputLbl = fresh_label () in 
  let inputBlock = {statements = []; terminator = Some (SwitchInt (e, [(0,cfgFalse.input)], cfgTrue.input))} in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = 
    BlockMap.union (fun _ _ _ -> None) ((addGoto outputLbl cfgFalse).blocks)
      ((BlockMap.union (fun _ _ _ -> None) ((addGoto outputLbl cfgTrue).blocks))
       (BlockMap.add outputLbl outputBlock (BlockMap.singleton inputLbl inputBlock)))
  }

let buildSwitch (e : AstThir.expression) (blocks : (int * cfg) list) (cfg : cfg): cfg = 
  let input = fresh_label () in 
  let cases = List.map (fun (value, cfg) -> (value, cfg.input)) blocks in 
  let bb1 = {statements = []; terminator = Some (SwitchInt (e, cases, cfg.input))} in
  let output = fresh_label () in
  let bb2 = {statements = []; terminator = None} in
  {
    input = input;
    output = output;
    blocks = 
      List.fold_left (fun r bb -> BlockMap.union (fun _ _ _ -> None) bb.blocks r) 
        (BlockMap.add output bb2 (BlockMap.singleton input bb1))
        (List.map (fun x  -> addGoto output (snd x))  blocks)
  }

let buildLoop (e : AstThir.expression) (cfg : cfg) : cfg = 
  let headLbl = fresh_label () in
  let outputLbl = fresh_label () in
  let headBlock = {statements = []; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  let outputBlock = {statements = []; terminator = None} in
  {
    input = headLbl;
    output = headLbl;
    blocks = 
      BlockMap.union (fun _ _ _ -> None) (addGoto outputLbl cfg).blocks
      (BlockMap.add outputLbl outputBlock (BlockMap.singleton headLbl headBlock))
  }

let buildInvoke (id : string) (el : AstThir.expression list) : cfg =
  let invokeLbl = fresh_label () in 
  let returnLbl = fresh_label () in
  let invokeBlock = {statements = []; terminator = Some (Invoke {id = id; params = el; next = returnLbl})} in
  let returnBlock = {statements = []; terminator = None} in 
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.add returnLbl returnBlock (BlockMap.singleton invokeLbl invokeBlock)
  }

let buildReturn (e : AstThir.expression option) =
  let returnLbl = fresh_label () in
  let returnBlock = {statements=[]; terminator= Some (Return e)} in 
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }

module Pass : Common.Pass.Body with
              type in_body = AstThir.expression AstHir.statement and   
              type out_body = cfg = 
struct
  type in_body = AstThir.expression AstHir.statement   
  type out_body = cfg

  let translate s _ _: cfg =
    let rec aux = function
      | AstHir.DeclVar(loc, b, id, stype, _v) -> 
        buildSingle [AstMir.DeclVar (loc, b, id, stype)]
      | DeclSignal _ -> failwith "not_implemented"    
      | Skip _ -> buildSingle []
      | Assign (loc, e1, e2) -> 
        buildSingle [AstMir.Assign (loc, e1, e2)]
      | Seq (_, s1, s2) ->
        buildSeq (aux s1) (aux s2)
      | Par _ -> failwith "not implemented" 
      | If (_loc, e, s, None) -> 
        buildIfThen e (aux s)
      | If (_loc, e, s1, Some s2) -> 
        buildIfThenElse e (aux s1) (aux s2)
      | While (_loc, e, s) -> 
        buildLoop e (aux s)
      | Case _ -> failwith "not implemented"
      | Invoke (_loc, _, id, el) -> buildInvoke id el
      | Return (_, e) -> buildReturn e
      | Run _ -> failwith "not implemented"
      | Emit _ -> failwith "not implemented"
      | Await _ -> failwith "not implemented"
      | When _ -> failwith "not implemented"
      | Watching _ -> failwith "not implemented"
      | Block _ -> failwith "not implemented"
    in aux s
end
