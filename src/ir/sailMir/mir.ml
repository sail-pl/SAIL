open AstMir
open IrThir
open Common 
open TypesCommon
open Result
open Pass
open MonadOption


module C = MonadCounter.M
module E = Error.MonadError
module CE = Error.MonadErrorTransformer(C)

open Monad.MonadSyntax(C)

let rename (src : label) (tgt : label) (t : terminator) : terminator = 
  match t with 
    | Goto lbl when lbl = src -> Goto tgt 
    | Invoke {id ; params ; next} -> Invoke {id ; params; next}
    | SwitchInt (st, l, deflt) -> 
      SwitchInt (st, List.map (fun (x, lbl) -> (x, if lbl = src then tgt else lbl)) l, 
        if src = deflt then tgt else deflt)
    | _ -> t

let emptyBasicBlock : cfg C.t = 
    let+ lbl = C.fresh in
    {
      input = lbl;
      output = lbl;
      blocks = BlockMap.singleton lbl {assignments = []; terminator=None}
    }

let singleBlock (bb : basicBlock) : cfg C.t = 
    let+ lbl = C.fresh in    
    {
      input = lbl;
      output = lbl;
      blocks = BlockMap.singleton lbl bb
    }

let assignBasicBlock (a : assignment) : cfg C.t = 
  let+ lbl = C.fresh in
  let bb = {assignments = [a]; terminator=None}  in 
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }

exception InvalidOutputNode

let disjointUnion = BlockMap.union (fun _ _ _ -> failwith "illegal label sharing")

let buildSeq (cfg1 : cfg) (cfg2 : cfg) : cfg = 
  let left = try BlockMap.find cfg1.output cfg1.blocks 
  with Not_found -> failwith "not found1"
  in 
  let res = 
  match left.terminator with 
  | Some (Invoke _) -> raise InvalidOutputNode (* Handle other cases*)
  | Some _ -> 
    {
      input = cfg1.input;
      output = cfg2.output;
      blocks = disjointUnion cfg1.blocks cfg2.blocks
    }
  | None -> 
    let right = 
      try BlockMap.find cfg2.input cfg2.blocks 
      with Not_found -> failwith "not found2" 
    in let bb = {assignments = left.assignments@right.assignments; terminator = right.terminator} in
    {
      input = cfg1.input;
      output = if cfg2.input = cfg2.output then cfg1.output else cfg2.output;
      blocks =
        let left = BlockMap.remove cfg1.output cfg1.blocks in 
        let right = BlockMap.map 
                      (fun {assignments; terminator} -> 
                        {assignments; 
                          terminator = M.fmap (rename cfg2.input cfg1.output) terminator}) 
                      (BlockMap.remove cfg2.input cfg2.blocks) in       
        BlockMap.add cfg1.output bb (disjointUnion left right)
     }
    in 
    res

let addGoto (lbl : label) (cfg : cfg) : cfg C.t = 
  let bb = {assignments=[]; terminator=Some (Goto lbl)} in
  let+ cfg' = singleBlock bb in 
  buildSeq cfg cfg'


let buildIfThen (e : Thir.expression) (cfg : cfg) : cfg C.t =
  let* outputLbl = C.fresh in
  let outputBlock = {assignments = []; terminator = None} in
  let* inputLbl = C.fresh in 
  let inputBlock = {assignments = []; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  let+ goto = addGoto outputLbl cfg in
   {
    input = inputLbl;
    output = outputLbl;
    blocks = 
      BlockMap.union (fun _ _ _ -> None) (goto.blocks )
      (BlockMap.add outputLbl outputBlock (BlockMap.singleton inputLbl inputBlock))
    }


let buildIfThenElse (e : Thir.expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg C.t = 
  let* outputLbl = C.fresh in 
  let outputBlock = {assignments = []; terminator = None} in
  let* inputLbl = C.fresh in 
  let inputBlock = {assignments = []; terminator = Some (SwitchInt (e, [(0,cfgFalse.input)], cfgTrue.input))} in
  let+ gotoF = addGoto outputLbl cfgFalse and* gotoT = addGoto outputLbl cfgTrue in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = 
    BlockMap.union (fun _ _ _ -> None) (gotoF.blocks)
      ((BlockMap.union (fun _ _ _ -> None) (gotoT.blocks))
       (BlockMap.add outputLbl outputBlock (BlockMap.singleton inputLbl inputBlock)))
  }


let buildSwitch (e : Thir.expression) (blocks : (int * cfg) list) (cfg : cfg): cfg C.t = 
  let open Monad.MonadFunctions(C) in
  let* input = C.fresh in 
  let* output = C.fresh in 
  let+ gotos = listMapM (fun (_,cfg) -> addGoto output cfg) blocks in 
  
  let cases = List.map (fun (value, cfg) -> (value, cfg.input)) blocks in 
  let bb1 = {assignments = []; terminator = Some (SwitchInt (e, cases, cfg.input))} in
  let bb2 = {assignments = []; terminator = None} in
  {
    input = input;
    output = output;
    blocks = 
      List.fold_left (fun r bb -> BlockMap.union (fun _ _ _ -> None) bb.blocks r)
      (BlockMap.add output bb2 (BlockMap.singleton input bb1))
      gotos
        
  }

let buildLoop (e : Thir.expression) (cfg : cfg) : cfg C.t = 
  let* headLbl = C.fresh in 
  let* outputLbl = C.fresh in 
  let+ goto = addGoto outputLbl cfg in
  let headBlock = {assignments = []; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  let outputBlock = {assignments = []; terminator = None} in
  {
    input = headLbl;
    output = outputLbl; (* false jumps here *)
    blocks = 
      BlockMap.union (fun _ _ _ -> None) goto.blocks
      (BlockMap.add outputLbl outputBlock (BlockMap.singleton headLbl headBlock))
  }

let buildInvoke (id : string) (el : Thir.expression list) : cfg C.t =
  let* invokeLbl = C.fresh in 
  let+ returnLbl = C.fresh in 
  let invokeBlock = {assignments = []; terminator = Some (Invoke {id = id; params = el; next = returnLbl})} in
  let returnBlock = {assignments = []; terminator = None} in 
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.add returnLbl returnBlock (BlockMap.singleton invokeLbl invokeBlock)
  } 

let buildReturn (e : Thir.expression option) : cfg C.t =
  let+ returnLbl = C.fresh in
  let returnBlock = {assignments=[]; terminator= Some (Return e)} in 
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }


let texpr (e : Thir.expression) : AstMir.expression = 
  let rec aux e : AstMir.expression = 
  match (e:Thir.expression) with 
    | Variable (lt, id) -> Variable (lt, id) 
    | Deref (lt, e) -> Deref (lt, aux e)
    | StructRead (lt, e, id) -> StructRead (lt, aux e, id)
    | ArrayRead (lt, e1, e2) -> ArrayRead (lt, aux e1, aux e2)
    | Literal (lt, l) -> Literal (lt, l)
    | UnOp (lt, o, e) -> UnOp (lt, o, aux e)
    | BinOp (lt, o ,e1, e2) -> BinOp(lt, o, aux e1, aux e2)
    | Ref (lt, b, e) -> Ref(lt, b, aux e)
    | ArrayStatic (lt, el) -> ArrayStatic (lt, List.map aux el)
    | StructAlloc (lt, id, m) -> StructAlloc(lt, id, FieldMap.map aux m)
    | EnumAlloc(lt, id, el) -> EnumAlloc(lt, id, List.map aux el)
  in aux e

let seqOfList (l : statement list) : statement = 
  List.fold_left (fun s l : statement -> Seq (dummy_pos, s, l)) (Skip dummy_pos) l

module Pass : Body with
              type in_body = Thir.statement and   
              type out_body = declaration list * cfg = 
struct
  type in_body = Thir.statement
  type out_body = declaration list * cfg


  open Monad.MonadSyntax(CE)
  open Monad.MonadOperator(C)

  let lower decl _ : (declaration list * cfg)  E.t =
    let rec aux : Thir.statement -> (declaration list * cfg) CE.t = function
      | DeclVar(loc, b, id, Some stype, None) -> 
        
        emptyBasicBlock >>| fun bb ->
        (
          [{location=loc; mut=b; id=id; varType=stype}],bb
        ) |> E.lift

      | DeclVar(loc, b, id, Some stype, Some e) -> 
        assignBasicBlock ({location=loc; target=Variable ((loc, stype), id); expression = texpr e})
        >>| fun bn ->
        ( 
          [{location=loc; mut=b; id=id; varType=stype}],bn
          (* ++ other statements *)
        ) |> E.lift

      | DeclVar _ as s -> error [Thir.extract_statements_loc s, "Declaration should have type "] |> C.lift (* -> add generic parameter to statements *)

      | Skip _ -> 
        emptyBasicBlock >>| fun bb -> ([],  bb) |> E.lift
      | Assign (loc, e1, e2) -> 
        assignBasicBlock ({location=loc; target=texpr e1; expression = texpr e2}) >>| fun bb ->
        (
          [],bb
        ) |> E.lift
        
      | Seq (_, s1, s2) ->
        let+ d1, cfg1 = aux s1 and* d2, cfg2 = aux s2 in
        d1@d2, buildSeq cfg1 cfg2

      | If (_loc, e, s, None) -> 
        let* d, cfg = aux s in
        buildIfThen (texpr e) cfg >>| fun ite ->
        (d,ite) |> E.lift
        
      | If (_loc, e, s1, Some s2) -> 
        let* d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        buildIfThenElse (texpr e) cfg1 cfg2 >>| fun ite ->
        (d1@d2, ite) |> E.lift

      | While (_loc, e, s) ->  
        let* d, cfg = aux s in 
        buildLoop (texpr e) cfg >>| fun l -> 
        (d, l) |> E.lift
        
      | Invoke (_loc, _, id, el) -> buildInvoke id (List.map texpr el) >>| fun invoke ->
        ([], invoke) |> E.lift
      | Return (_, e) ->
        let e = match e with None -> None | Some e -> Some (texpr e) in 
        buildReturn e >>| fun ret ->
        ([], ret) |> E.lift

      | Run _ | Emit _ | Await _ | When _  | Watching _ 
      | Par _  | Case _ | DeclSignal _ as s -> error [Thir.extract_statements_loc s, "unimplemented"] |> C.lift

      | Block (_loc, s) -> aux s
    in aux decl.body 0 |> fst
  end