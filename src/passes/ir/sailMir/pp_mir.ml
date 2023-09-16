open Common
open PpCommon
open Format
open MirAst 
open TypesCommon

let rec ppPrintExpression (pf : Format.formatter) (e : MirAst.expression) : unit =
  match e.node with 
    | Variable s -> fprintf pf "%s" s
    | Deref e -> fprintf pf "*%a" ppPrintExpression e 
    | StructRead2 s -> fprintf pf "%a.%s" ppPrintExpression s.value.strct s.value.field.value
    | ArrayRead a -> fprintf pf "%a[%a]" ppPrintExpression a.array ppPrintExpression a.idx
    | Literal (l) -> fprintf pf "%a" PpCommon.pp_literal l 
    | UnOp (o, e) -> fprintf pf "%a %a" pp_unop o ppPrintExpression e
    | BinOp bop -> fprintf pf "%a %a %a" ppPrintExpression bop.left pp_binop bop.op ppPrintExpression bop.right
    | Ref (true,e) -> fprintf pf "&mut %a" ppPrintExpression e 
    | Ref (false,e) -> fprintf pf "&%a" ppPrintExpression e 
    | ArrayStatic el ->  
      Format.fprintf pf "[%a]"
        (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    |StructAlloc2  s ->
      let pp_field pf (x, (y: 'a locatable)) = Format.fprintf pf "%s:%a" x ppPrintExpression y.value in
      Format.fprintf pf "%s{%a}" s.value.name.value
        (Format.pp_print_list ~pp_sep:pp_comma pp_field) s.value.fields
    | EnumAlloc (id,el) ->  
      Format.fprintf pf "[%s(%a)]" id.value
        (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) el

let ppPrintPredecessors (pf : Format.formatter) (preds : LabelSet.t ) : unit = 
  if LabelSet.is_empty preds then fprintf pf "// no precedessors"
  else fprintf pf "// predecessors : %a" (pp_print_seq ~pp_sep:pp_comma pp_print_int) (LabelSet.to_seq preds)

let ppPrintDeclaration (pf : Format.formatter) (d : declaration) : unit = 
  if d.mut then
    fprintf pf "\tlet mut %s : %a" d.id pp_type d.varType 
  else fprintf pf "\tlet %s : %a" d.id pp_type d.varType
let ppPrintAssignement (pf : Format.formatter) (a : assignment) : unit = 
  fprintf pf "\t\t%a = %a" ppPrintExpression a.target ppPrintExpression a.expression

let ppPrintTerminator (pf : Format.formatter) (t : terminator) : unit = 
  match t with 
    | Goto lbl -> fprintf pf "\t\tgoto %d;" lbl 
    | Invoke {id; params;next;origin;target} -> fprintf pf "\t\t%a%s(%a) -> [return: bb%d]" 
          (Format.pp_print_option  (fun fmt id -> fprintf fmt "%s = %s::" id origin.value)) target 
          id 
          (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) params 
          next
    | Return None -> fprintf pf "\t\treturn;"
    | Return (Some e) ->  fprintf pf "\t\treturn %a;" ppPrintExpression e 
    | SwitchInt si -> 
      let pp_case pf (x, y) = Format.fprintf pf "%d:%d" x y in
      fprintf pf "\t\tswitchInt(%a) [%a, otherwise: %d]" 
        ppPrintExpression si.choice
        (Format.pp_print_list ~pp_sep:pp_comma pp_case) si.paths
        si.default
    | Break -> failwith "can't happen"

let ppPrintFrame (pf : Format.formatter) (f : VE.frame) =
  let print_var (pf : Format.formatter) (id,(_,{ty;_}):string * VE.variable) =
  Format.fprintf pf "(%s:%a)" id pp_type ty
  in
  Format.fprintf pf "[%a]" (Format.pp_print_list ~pp_sep:pp_comma print_var) (TypesCommon.FieldMap.bindings f)

let ppPrintBasicBlock (pf : Format.formatter) (lbl : label) (bb : (VE.t,unit) basicBlock) : unit = 
  let _pp_env pf bb = 
    Format.fprintf pf "%a" (Format.pp_print_list ~pp_sep:pp_force_newline ppPrintFrame) bb.forward_info in

  let pp_preds pf bb = 
    Format.fprintf pf "%a\n" ppPrintPredecessors bb.predecessors in

  let pp_block pf bb = 
    match bb.terminator with 
      None ->
        Format.fprintf pf "%a\n" (Format.pp_print_list ~pp_sep:pp_semicr ppPrintAssignement) bb.assignments 
      |Some t ->
      Format.fprintf pf "%a\n%a" (Format.pp_print_list ~pp_sep:pp_semicr ppPrintAssignement) bb.assignments  ppPrintTerminator t 
  in 
  Format.fprintf pf "\tbb%d%a\t{\n%a\n\n\t}\n" lbl pp_preds bb pp_block bb 
  (* Format.fprintf pf "\tbb%d%a\t{\n\t\tenv [%a]%a\n\n\t}\n" lbl pp_preds bb pp_env bb pp_block bb  *)

(* termination *)
let ppPrintCfg (pf : Format.formatter) (cfg : cfg) : unit = 
  Format.fprintf pf "\n\t//input block %d output block %d\n\n" cfg.input cfg.output;
  let check = ref [] in
  let rec aux (lbl : label) : unit =
    if List.mem lbl !check then () else 
    let () = check := lbl::!check in
    let bb = 
      try BlockMap.find lbl cfg.blocks 
    with Not_found -> failwith "No such node"
    in
    let _ = Format.fprintf pf "%a" (fun x -> ppPrintBasicBlock x lbl) bb in
    match bb.terminator with 
      | None -> ()
      | Some t -> match t with
        | Goto lbl -> aux lbl
        | Invoke i -> aux i.next
        | Return _ -> ()
        | SwitchInt si -> 
          let _ = List.iter aux (List.map snd si.paths) in 
          aux si.default
        | Break -> failwith "can't happen"
  in 
    aux cfg.input;
    List.iter (fun (lbl, bb) -> if not (List.mem lbl !check) then 
      Format.fprintf pf "%a" (fun x -> ppPrintBasicBlock x lbl) bb) 
      (BlockMap.bindings cfg.blocks)

let ppPrintMethodSig (pf : Format.formatter) (s : TypesCommon.method_sig) : unit = 
  match s.rtype with 
  None ->
    fprintf pf "%s(%a)" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params
| Some t -> 
    fprintf pf "%s(%a) -> %a" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params pp_type t

let ppPrintMethod (pf : Format.formatter) (m: (declaration list * cfg) TypesCommon.method_defn) : unit = 
  match m.m_body with
  | Right (decls,cfg) ->  fprintf pf  "fn %a{\n%a\n%a}\n"  ppPrintMethodSig m.m_proto (pp_print_list ~pp_sep:pp_semicr ppPrintDeclaration) decls ppPrintCfg cfg
  | Left _ -> fprintf pf "extern fn %a\n" ppPrintMethodSig m.m_proto


(* let ppPrintProcess (pf : Format.formatter) (p : (declaration list * cfg) Common.TypesCommon.process_defn) : unit = 
  fprintf pf  "proc %s() {\n%a\n%a}\n" p.p_name (pp_print_list ~pp_sep:pp_semicr ppPrintDeclaration) (fst p.p_body) ppPrintCfg (snd p.p_body) *)


let ppPrintModule (pf : Format.formatter) (m : (declaration list * cfg,_) SailModule.methods_processes SailModule.t ) : unit = 
  fprintf pf "// Sail MIR Representation: %s\n%a" m.md.name 
  (pp_print_list ppPrintMethod) m.body.methods
  (* (pp_print_list ~pp_sep:pp_comma ppPrintProcess) m.body.processes *)