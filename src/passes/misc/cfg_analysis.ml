open Common
open TypesCommon
open Pass
open IrMir
open SailParser
open IrHir
open AstMir
open Monad


module E  = Error.Logger
open UseMonad(E)
let cfg_returns ({input;blocks;_} : cfg) : (loc option * _ basicBlock BlockMap.t) E.t = 
  let rec aux lbl blocks = 
    let blocks' = BlockMap.remove lbl blocks in
    match BlockMap.find_opt lbl blocks with
    | None -> (None, blocks') |> E.pure
    | Some bb -> 
      begin
      match bb.terminator with
      | None -> (Some bb.location, blocks') |> E.pure
      | Some Break -> E.throw @@ Error.make bb.location "there should be no break at this point" >>= fun () -> aux input blocks'
      | Some Return _ -> (None, blocks') |> E.pure
      | Some (Invoke {next;_}) -> aux next blocks'
      | Some (Goto lbl) -> aux lbl blocks'
      | Some (SwitchInt si) -> 
        let* x = aux si.default blocks' in 
        ListM.fold_left (fun (_,b) (_,lbl) -> aux lbl b) x si.paths
    end
  in
  aux input blocks

let check_unreachable (proto : method_sig) (_,cfg : mir_function) : unit E.t = 
  let* ret,unreachable_blocks = cfg_returns cfg in
  if Option.is_some ret && proto.rtype <> None then 
    E.throw @@ Error.make (Option.get ret) @@ Printf.sprintf "%s doesn't always return !" proto.name
  else
    let () = BlockMap.iter (fun lbl {location=_;_} ->  Logs.debug (fun m -> m "unreachable block %i" lbl)) unreachable_blocks in
    let blocks = BlockMap.filter (fun _ {location;_} -> location <> dummy_pos) unreachable_blocks in
    match BlockMap.choose_opt blocks with
    | Some (_,bb) -> 
      let _loc = match List.nth_opt bb.assignments 0 with
      | Some v -> v.location
      | None ->  bb.location in
      E.throw @@ Error.make bb.location "unreachable code"
    | None -> E.pure ()


let check_returns  (proto : method_sig) (decls,cfg : mir_function) : mir_function E.t = 
  let open MirUtils.Traversal(E) in
  let check block = 
    match block.terminator,proto.rtype with
    | None,None -> (* we insert void return when return type is void*) 
      E.pure {block with terminator= Some (Return None)} 
    | None,Some _  -> 
      E.throw Error.(make proto.pos
      @@ Printf.sprintf "no return statement but must return %s" 
      @@ string_of_sailtype proto.rtype)
    | _ -> E.pure block
  in 

  let+ blocks = forward cfg.input cfg.blocks check in 
  decls,{cfg with blocks}

module Pass = Make(struct 
  let name = "analysis on mir"
  type in_body = (AstMir.mir_function,(HirUtils.statement,HirUtils.expression) AstParser.process_body) SailModule.methods_processes
  type out_body = in_body

  let transform (sm: in_body SailModule.t) : out_body SailModule.t E.t =
    let+ methods = ListM.map (
      fun f -> 
        let+ m_body = match f.m_body with
                    | Left _ -> E.pure f.m_body 
                    | Right b ->
                      check_unreachable f.m_proto b >>= fun () -> 
                      check_returns f.m_proto b >>| fun b -> Either.right b in
        {f with m_body}
    ) sm.body.methods in
    
  {sm with body = {sm.body with methods} }
end
)

