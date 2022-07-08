open AstMir
open IrHir
open IrThir
open Common 
open TypesCommon
open Result
open Pass
open MonadOption
open Monad.MonadSyntax(Error.MonadError)


let label_cpt = ref 0


let var_cpt = ref 0 

let fresh_var () =
  let fresh = !var_cpt in 
  let _ = incr var_cpt in "_"^(string_of_int fresh)


(* module P = Writer.Writer.Make (Monoid.MonoidList (struct type t = AstMir.expression AstHir.statement end))


let simplifyExpression (e : Thir.expression) : AstMir.expression P.t  =
  let open Monad.MonadSyntax(P) in
  let open Monad.MonadFunctions(P) in
  let rec aux e : AstMir.expression P.t  = 
  match e with
  | AstHir.Variable _ | AstHir.Literal _ -> return e
  | AstHir.Deref (lt, e) -> 
      let* e = aux e in return (AstHir.Deref (lt, e))
  | AstHir.StructRead (lt, e, f) -> 
      let* e = aux e in return (AstHir.StructRead (lt, e, f))
  | AstHir.ArrayRead (lt, e1, e2) -> 
      let* e1 = aux e1 in 
      let* e2 = aux e2 in 
      return (AstHir.ArrayRead (lt, e1, e2))
  | AstHir.UnOp (lt, o, e) -> 
      let* e = aux e in return (AstHir.UnOp (lt,o,e))
  | AstHir.BinOp (lt, o, e1, e2) -> 
      let* e1 = aux e1 in 
      let* e2 = aux e2 in 
      return (AstHir.BinOp(lt, o,e1, e2))
  | AstHir.Ref (lt, b, e) -> 
      let* e = aux e in return (AstHir.Ref(lt, b, e))
  | AstHir.ArrayStatic (lt, el) ->
      let* el = listMapM aux el in return (AstHir.ArrayStatic(lt, el))
  | AstHir.StructAlloc (lt, id, em) -> 
    let* em = mapMapM aux em in return (AstHir.StructAlloc(lt, id, em))
  | AstHir.EnumAlloc (lt, id, el) ->
    let* el = listMapM aux el in return (AstHir.EnumAlloc (lt, id, el))
  in aux e *)

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

let emptyBasicBlock () = 
  let lbl = fresh_label () in
    {
      input = lbl;
      output = lbl;
      blocks = BlockMap.singleton lbl {assignments = []; terminator=None}
    }

let singleBlock (bb : basicBlock) : cfg = 
  let lbl = fresh_label () in
    {
      input = lbl;
      output = lbl;
      blocks = BlockMap.singleton lbl bb
    }

let assignBasicBlock (a : assignment) = 
  let lbl = fresh_label () in
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

let addGoto (lbl : label) (cfg : cfg) : cfg = 
  let bb = {assignments=[]; terminator=Some (Goto lbl)} in
  let cfg' = singleBlock bb in 
  buildSeq cfg cfg' 

  let buildIfThen (e : Thir.expression) (cfg : cfg) : cfg = 
    let outputLbl = fresh_label () in
    let outputBlock = {assignments = []; terminator = None} in
    let inputLbl = fresh_label () in 
    let inputBlock = {assignments = []; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
    {
      input = inputLbl;
      output = outputLbl;
      blocks = 
        BlockMap.union (fun _ _ _ -> None) ((addGoto outputLbl cfg).blocks )
        (BlockMap.add outputLbl outputBlock (BlockMap.singleton inputLbl inputBlock))
    }

let buildIfThenElse (e : Thir.expression) (cfgTrue : cfg) (cfgFalse : cfg) : cfg = 
  let outputLbl = fresh_label () in
  let outputBlock = {assignments = []; terminator = None} in
  let inputLbl = fresh_label () in 
  let inputBlock = {assignments = []; terminator = Some (SwitchInt (e, [(0,cfgFalse.input)], cfgTrue.input))} in
  {
    input = inputLbl;
    output = outputLbl;
    blocks = 
    BlockMap.union (fun _ _ _ -> None) ((addGoto outputLbl cfgFalse).blocks)
      ((BlockMap.union (fun _ _ _ -> None) ((addGoto outputLbl cfgTrue).blocks))
       (BlockMap.add outputLbl outputBlock (BlockMap.singleton inputLbl inputBlock)))
  }

let buildSwitch (e : Thir.expression) (blocks : (int * cfg) list) (cfg : cfg): cfg = 
  let input = fresh_label () in 
  let cases = List.map (fun (value, cfg) -> (value, cfg.input)) blocks in 
  let bb1 = {assignments = []; terminator = Some (SwitchInt (e, cases, cfg.input))} in
  let output = fresh_label () in
  let bb2 = {assignments = []; terminator = None} in
  {
    input = input;
    output = output;
    blocks = 
      List.fold_left (fun r bb -> BlockMap.union (fun _ _ _ -> None) bb.blocks r) 
        (BlockMap.add output bb2 (BlockMap.singleton input bb1))
        (List.map (fun x  -> addGoto output (snd x))  blocks)
  }

let buildLoop (e : Thir.expression) (cfg : cfg) : cfg = 
  let headLbl = fresh_label () in
  let outputLbl = fresh_label () in
  let headBlock = {assignments = []; terminator = Some (SwitchInt (e, [(0,outputLbl)], cfg.input))} in
  let outputBlock = {assignments = []; terminator = None} in
  {
    input = headLbl;
    output = outputLbl; (* false jumps here *)
    blocks = 
      BlockMap.union (fun _ _ _ -> None) (addGoto outputLbl cfg).blocks
      (BlockMap.add outputLbl outputBlock (BlockMap.singleton headLbl headBlock))
  }

let buildInvoke (id : string) (el : Thir.expression list) : cfg =
  let invokeLbl = fresh_label () in 
  let returnLbl = fresh_label () in
  let invokeBlock = {assignments = []; terminator = Some (Invoke {id = id; params = el; next = returnLbl})} in
  let returnBlock = {assignments = []; terminator = None} in 
  {
    input = invokeLbl;
    output = returnLbl;
    blocks = BlockMap.add returnLbl returnBlock (BlockMap.singleton invokeLbl invokeBlock)
  }

let buildReturn (e : Thir.expression option) =
  let returnLbl = fresh_label () in
  let returnBlock = {assignments=[]; terminator= Some (Return e)} in 
  {
    input = returnLbl;
    output = returnLbl;
    blocks = BlockMap.singleton returnLbl returnBlock
  }


let texpr (e : Thir.expression) : AstMir.expression = 
  let rec aux e = 
  match e with 
    | AstHir.Variable (lt, id) -> AstHir.Variable (lt, id) 
    | AstHir.Deref (lt, e) -> AstHir.Deref (lt, aux e)
    | AstHir.StructRead (lt, e, id) -> AstHir.StructRead (lt, aux e, id)
    | AstHir.ArrayRead (lt, e1, e2) -> AstHir.ArrayRead (lt, aux e1, aux e2)
    | AstHir.Literal (lt, l) -> AstHir.Literal (lt, l)
    | AstHir.UnOp (lt, o, e) -> AstHir.UnOp (lt, o, aux e)
    | AstHir.BinOp (lt, o ,e1, e2) -> AstHir.BinOp(lt, o, aux e1, aux e2)
    | AstHir.Ref (lt, b, e) -> AstHir.Ref(lt, b, aux e)
    | AstHir.ArrayStatic (lt, el) -> AstHir.ArrayStatic (lt, List.map aux el)
    | AstHir.StructAlloc (lt, id, m) -> AstHir.StructAlloc(lt, id, FieldMap.map aux m)
    | AstHir.EnumAlloc(lt, id, el) -> AstHir.EnumAlloc(lt, id, List.map aux el)
  in aux e

let seqOfList (l : 'a AstHir.statement list) : 'a AstHir.statement = 
  List.fold_left (fun s l -> AstHir.Seq (dummy_pos, s, l)) (AstHir.Skip dummy_pos) l

module Pass  : Body with
              type in_body = Thir.statement and   
              type out_body = declaration list * cfg  = 
struct
  type in_body = Thir.statement
  type out_body = declaration list * cfg

  open Monad.MonadSyntax(Error.MonadError)
  open Error.MonadError
  let lower decl _ =
    label_cpt := 0;
    let rec aux : Thir.statement -> (declaration list * cfg) Error.MonadError.t = function
      | AstHir.DeclVar(loc, b, id, Some stype, None) ->
        (
          [{location=loc; mut=b; id=id; varType=stype}],emptyBasicBlock ()
        ) |> lift

      | AstHir.DeclVar(loc, b, id, Some stype, Some e) -> 
        (
          [{location=loc; mut=b; id=id; varType=stype}],
          assignBasicBlock ({location=loc; target=Variable ((loc, stype), id); expression = texpr e}) (* ++ other statements *)
        ) |> lift

      | AstHir.DeclVar _ as s -> error [Thir.extract_statements_loc s, "Declaration should have type "] (* -> add generic parameter to statements *)

      | AstHir.Skip _ -> ([], emptyBasicBlock ()) |> lift
      | AstHir.Assign (loc, e1, e2) -> 
        (
          [], assignBasicBlock ({location=loc; target=texpr e1; expression = texpr e2})
        ) |> lift
      | Seq (_, s1, s2) ->
        let+ d1, cfg1 = aux s1 and* d2, cfg2 = aux s2 in
        d1@d2, buildSeq cfg1 cfg2

      | If (_loc, e, s, None) -> 
        let+ d, cfg = aux s in d, buildIfThen (texpr e) cfg
      | If (_loc, e, s1, Some s2) -> 
        let+ d1,cfg1 = aux s1 and* d2,cfg2 = aux s2 in
        d1@d2, buildIfThenElse (texpr e) cfg1 cfg2
      | While (_loc, e, s) -> 
        let+ d, cfg = aux s in
        d, buildLoop (texpr e) cfg
      | Invoke (_loc, _, id, el) -> 
        ([], buildInvoke id (List.map texpr el)) |> lift
      | Return (_, e) ->
        let e = match e with None -> None | Some e -> Some (texpr e) in 
        ([], buildReturn e) |> lift

      | Run _ | Emit _ | Await _ | When _  | Watching _ 
      | Par _  | Case _ | AstHir.DeclSignal _ as s -> error [Thir.extract_statements_loc s, "unimplemented"]

      | Block (_loc, s) -> aux s
    in let+ res = aux decl.body in res
end
