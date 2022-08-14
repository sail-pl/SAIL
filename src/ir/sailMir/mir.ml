open AstMir
open IrThir
open Common 
open TypesCommon
open Result
open Monad


module C = MonadState.Counter
module E = Error.MonadError
module CE = struct 
  include Error.MonadErrorTransformer(MonadState.Counter)
  let fresh = C.fresh |> lift
end

open MonadSyntax(C)

let rename (src : label) (tgt : label) (t : terminator) : terminator = 
  match t with 
    | Goto lbl when lbl = src -> Goto tgt 
    | SwitchInt (st, l, deflt) -> 
      SwitchInt (st, List.map (fun (x, lbl) -> (x, if lbl = src then tgt else lbl)) l, 
        if src = deflt then tgt else deflt)
    | _ -> t

let emptyBasicBlock (location:loc) : cfg C.t = 
  let+ lbl = C.fresh in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl {assignments = []; location; terminator=None}
  }

let singleBlock (bb : basicBlock) : cfg C.t = 
  let+ lbl = C.fresh in    
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }

let assignBasicBlock (location : loc) (a : assignment) : cfg C.t = 
  let bb = {assignments = [a]; location; terminator=None}  in 
  let+ lbl = C.fresh in
  {
    input = lbl;
    output = lbl;
    blocks = BlockMap.singleton lbl bb
  }


let disjoint = (fun _ _ _ -> None) 
let assert_disjoint = (fun _ _ _ -> failwith "illegal label sharing")


let buildSeq (cfg1 : cfg) (cfg2 : cfg) : cfg E.t = 
  let left =  BlockMap.find cfg1.output cfg1.blocks 
  and right = BlockMap.find cfg2.input cfg2.blocks 
  in 
  match left.terminator with 
  | Some (Invoke _) -> error [left.location, "invalid output node"]
  (* todo: handle other cases *)
  | Some _ -> 
    {
      input = cfg1.input;
      output = cfg2.output;
      blocks = BlockMap.union assert_disjoint cfg1.blocks cfg2.blocks
    } |> ok
  | None -> 
    let bb = {assignments = left.assignments@right.assignments; location= right.location; terminator = right.terminator} in
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
     } |> ok

let addGoto  (lbl : label) (cfg : cfg) : cfg CE.t = 
  let bb = {assignments=[]; location = dummy_pos; terminator=Some (Goto lbl)} in
  let+ cfg' = singleBlock bb in 
  buildSeq cfg cfg'


let buildIfThen (location : loc) (e : expression) (cfg : cfg) : cfg CE.t =
  let open MonadSyntax(CE) in
  let outputBlock = {assignments = []; location = dummy_pos; terminator = None} in
  let* outputLbl = CE.fresh and* inputLbl = CE.fresh in 
  let+ goto = addGoto outputLbl cfg in
  let inputBlock = {assignments = []; location; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.singleton inputLbl inputBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint goto.blocks
  }


let buildIfThenElse (location : loc) (e : expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg CE.t = 
  let open MonadSyntax(CE) in
  let outputBlock = {assignments = []; location = dummy_pos; terminator = None}
  and inputBlock = {assignments = []; location; terminator = Some (SwitchInt (e, [(0,cfgFalse.input)], cfgTrue.input))} in
  
  let* inputLbl = CE.fresh and* outputLbl = CE.fresh in 
  let+ gotoF = addGoto outputLbl cfgFalse and* gotoT = addGoto outputLbl cfgTrue in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = BlockMap.singleton inputLbl inputBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint gotoT.blocks
              |> BlockMap.union disjoint gotoF.blocks
  }


let buildSwitch (e : expression) (blocks : (int * cfg) list) (cfg : cfg): cfg CE.t = 
  let open MonadSyntax(CE) in
  let cases = List.map (fun (value, cfg) -> (value, cfg.input)) blocks in 
  let bb1 = {assignments = []; location = dummy_pos; terminator = Some (SwitchInt (e, cases, cfg.input))}
  and bb2 = {assignments = []; location = dummy_pos; terminator = None} in

  let open MonadFunctions(CE) in
  let* input =  CE.fresh and* output = CE.fresh in 
  let+ gotos = listMapM (fun (_,cfg) -> addGoto output cfg) blocks in 
  {
    input = input;
    output = output;
    blocks = ( BlockMap.singleton input bb1 
                |> BlockMap.add output bb2  
                |> List.fold_left (fun r bb -> BlockMap.union disjoint bb.blocks r)
              ) gotos  
  }

let buildLoop (location : loc) (e : expression) (cfg : cfg) : cfg CE.t = 
  let open MonadSyntax(CE) in
  let outputBlock = {assignments = []; location; terminator = None} in
  let* inputLbl =  CE.fresh and* headLbl = CE.fresh and* outputLbl =  CE.fresh in 
  let+ goto = addGoto inputLbl cfg in
  let headBlock = {assignments = []; location = dummy_pos; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  {
    input = headLbl;
    output = outputLbl; (* false jumps here *)
    blocks = BlockMap.singleton inputLbl headBlock 
              |> BlockMap.add headLbl headBlock 
              |> BlockMap.add outputLbl outputBlock 
              |> BlockMap.union disjoint goto.blocks
  }

let buildInvoke (location : loc) (id : string) (target : string option) (el : expression list) : cfg C.t =
  let returnBlock = {assignments = []; location = dummy_pos; terminator = None} in 
  let+ invokeLbl = C.fresh and* returnLbl = C.fresh in 
  let invokeBlock = {assignments = []; location; terminator = Some (Invoke {id = id; target; params = el; next = returnLbl})} in
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.singleton invokeLbl invokeBlock 
              |> BlockMap.add returnLbl returnBlock 
  } 

let buildReturn (location : loc) (e : expression option) : cfg C.t =
  let returnBlock = {assignments=[]; location; terminator= Some (Return e)} in 
  let+ returnLbl = C.fresh in
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }


let texpr (e : Thir.expression) : expression = 
  let rec aux e : expression = 
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


(* todo: modify to use in mir *)
module V : Env.Variable = 
  struct 
  type t = sailtype
  let string_of_var v = string_of_sailtype (Some v)
  let to_var _ (t:sailtype) = t
end


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


  open MonadSyntax(CE)

  let lower_function decl _env : out_body  E.t =
    let rec aux : Thir.statement -> (declaration list * cfg) CE.t = function
      | DeclVar(loc, b, id, Some stype, None) -> 
        let+ bb = emptyBasicBlock loc |> CE.lift in
        [{location=loc; mut=b; id=id; varType=stype}],bb

      | DeclVar(loc, b, id, Some stype, Some e) -> 
        let+ bn = assignBasicBlock loc ({location=loc; target=Variable ((loc, stype), id); expression = texpr e}) |> CE.lift in
        [{location=loc; mut=b; id=id; varType=stype}],bn
        (* ++ other statements *)

      | DeclVar _ as s -> error [Thir.extract_statements_loc s, "Declaration should have type "] |> C.lift (* -> add generic parameter to statements *)

      | Skip loc -> let+ bb = emptyBasicBlock loc |> CE.lift in ([],  bb)

      | Assign (loc, e1, e2) -> 
        let+ bb = assignBasicBlock loc ({location=loc; target=texpr e1; expression = texpr e2}) |> CE.lift in [],bb
        
      | Seq (_, s1, s2) ->
        let* d1, cfg1 = aux s1 and* d2, cfg2 = aux s2 in
        let open MonadOperator(E) in 
        buildSeq cfg1 cfg2 >>| (fun bb -> (d1@d2,bb)) |> C.lift

      | If (loc, e, s, None) -> 
        let* d, cfg = aux s in
        let+ ite = buildIfThen loc (texpr e) cfg in
        (d,ite) 
        
      | If (loc, e, s1, Some s2) -> 
        let* d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        let+ ite = buildIfThenElse loc (texpr e) cfg1 cfg2 in
        (d1@d2, ite) 

      | While (loc, e, s) ->  
        let* d, cfg = aux s in 
        let+ l = buildLoop loc (texpr e) cfg in
        (d, l)
        
      | Invoke (loc, target, id, el) -> let+ invoke = buildInvoke loc id target (List.map texpr el) |> CE.lift in
        ([], invoke)

      | Return (loc, e) ->
        let e = match e with None -> None | Some e -> Some (texpr e) in 
        let+ ret =  buildReturn loc e |> CE.lift in
        ([], ret)

      | Run _ | Emit _ | Await _ | When _  | Watching _ 
      | Par _  | Case _ | DeclSignal _ as s -> error [Thir.extract_statements_loc s, "unimplemented"] |> C.lift

      | Block (_loc, s) -> aux s
    in 
    Logs.debug (fun m -> m "lowering to MIR %s" decl.name);
    let open MonadSyntax(E) in
    let* (decls,cfg) as res = aux decl.body 0 |> fst in
    
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
