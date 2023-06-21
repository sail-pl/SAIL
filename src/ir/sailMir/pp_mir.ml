open Common
open PpCommon
open Format
open AstMir 

let rec ppPrintExpression (pf : Format.formatter) (e : AstMir.expression) : unit =
  match e.exp with 
    | Variable s -> fprintf pf "%s" s
    | Deref e -> fprintf pf "*%a" ppPrintExpression e 
    | StructRead (e, s) -> fprintf pf "%a.%s" ppPrintExpression e s
    | ArrayRead (e1, e2) -> fprintf pf "%a[%a]" ppPrintExpression e1 ppPrintExpression e2
    | Literal (l) -> fprintf pf "%a" PpCommon.pp_literal l 
    | UnOp (o, e) -> fprintf pf "%a %a" pp_unop o ppPrintExpression e
    | BinOp ( o, e1, e2) -> fprintf pf "%a %a %a" ppPrintExpression e1 pp_binop o ppPrintExpression e2
    | Ref (true,e) -> fprintf pf "&mut %a" ppPrintExpression e 
    | Ref (false,e) -> fprintf pf "&%a" ppPrintExpression e 
    | ArrayStatic el ->  
      Format.fprintf pf "[%a]"
        (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    |StructAlloc  (id, m) ->
      let pp_field pf (x, y) = Format.fprintf pf "%s:%a" x ppPrintExpression y in
      Format.fprintf pf "%s{%a}" (snd id)
        (Format.pp_print_list ~pp_sep:pp_comma pp_field)
        m
    | EnumAlloc (id,el) ->  
      Format.fprintf pf "[%s(%a)]" (snd id)
        (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    | MethodCall _ -> ()

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
    | Invoke {id; params;next;origin;target} -> fprintf pf "\t\t%a%s(%a) -> %d" (Format.pp_print_option  (fun fmt id -> fprintf fmt "%s = %s::" id origin.mname)) target id (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) params next
    | Return None -> fprintf pf "\t\treturn;"
    | Return (Some e) ->  fprintf pf "\t\treturn %a;" ppPrintExpression e 
    | SwitchInt (e, cases, default) -> 
      let pp_case pf (x, y) = Format.fprintf pf "%d:%d" x y in
      fprintf pf "\t\tswitchInt(%a) [%a, otherwise: %d]" 
        ppPrintExpression e 
        (Format.pp_print_list ~pp_sep:pp_comma pp_case) cases
        default
    | Break -> failwith "can't happen"

let ppPrintFrame (pf : Format.formatter) (f : VE.frame) =
  let print_var (pf : Format.formatter) (id,(_,{ty;_}):string * VE.variable) =
  Format.fprintf pf "(%s:%a)" id pp_type ty
  in
  Format.fprintf pf "[%a]" (Format.pp_print_list ~pp_sep:pp_comma print_var) (TypesCommon.FieldMap.bindings f)

let ppPrintBasicBlock (pf : Format.formatter) (lbl : label) (bb : basicBlock) : unit = 
  let pp_env pf bb = 
    Format.fprintf pf "%a" (Format.pp_print_list ~pp_sep:pp_force_newline ppPrintFrame) bb.env.stack in

  let pp_preds pf bb = 
    Format.fprintf pf "%a\n" ppPrintPredecessors bb.predecessors in

  let pp_block pf bb = 
    match bb.terminator with 
      None ->
        Format.fprintf pf "%a\n" (Format.pp_print_list ~pp_sep:pp_semicr ppPrintAssignement) bb.assignments 
      |Some t ->
      Format.fprintf pf "%a\n%a" (Format.pp_print_list ~pp_sep:pp_semicr ppPrintAssignement) bb.assignments  ppPrintTerminator t 
  in 
  Format.fprintf pf "\tbb%d%a\t{\n\t\tenv [%a]%a\n\n\t}\n" lbl pp_preds bb pp_env bb pp_block bb 

(* termination *)
let ppPrintCfg (pf : Format.formatter) (cfg : cfg) : unit = 
  let _ = Format.fprintf pf "\t//input block %d output block %d\n" cfg.input cfg.output in
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
        | SwitchInt (_, cases, default) -> 
          let _ = List.iter aux (List.map snd cases) in 
          aux default
        | Break -> failwith "can't happen"
  in 
    aux cfg.input;
    List.iter (fun (lbl, bb) -> if not (List.mem lbl !check) then 
      Format.fprintf pf "%a" (fun x -> ppPrintBasicBlock x lbl) bb) 
      (BlockMap.bindings cfg.blocks)

let ppPrintMethodSig (pf : Format.formatter) (s : Common.TypesCommon.method_sig) : unit = 
  match s.rtype with 
  None ->
    fprintf pf "%s(%a)" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params
| Some t -> 
    fprintf pf "%s(%a) -> %a" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params pp_type t

let ppPrintMethod (pf : Format.formatter) (m: (declaration list * cfg) Common.TypesCommon.method_defn) : unit = 
  match m.m_body with
  | Right (decls,cfg) ->  fprintf pf  "fn %a{\n%a\n%a}\n"  ppPrintMethodSig m.m_proto (pp_print_list ~pp_sep:pp_semicr ppPrintDeclaration) decls ppPrintCfg cfg
  | Left _ -> fprintf pf "extern fn %a\n" ppPrintMethodSig m.m_proto
 

let ppPrintProcess (pf : Format.formatter) (p : (declaration list * cfg) Common.TypesCommon.process_defn) : unit = 
  fprintf pf  "proc %s() {\n%a\n%a}\n" p.p_name (pp_print_list ~pp_sep:pp_semicr ppPrintDeclaration) (fst p.p_body) ppPrintCfg (snd p.p_body)


let ppPrintModule (pf : Format.formatter) (m : (declaration list * cfg) Common.SailModule.t ) : unit = 
  fprintf pf "// Sail MIR Representation: %s\n%a \n%a" m.md.name 
  (pp_print_list ppPrintMethod) m.methods
  (pp_print_list ~pp_sep:pp_comma ppPrintProcess) m.processes