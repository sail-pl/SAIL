open Common
open PpCommon
open Format
open AstMir 
open IrThir

let rec ppPrintExpression (pf : Format.formatter) (e : Thir.expression) : unit =
  match e with 
    | Variable ((_, _), s) -> print_string s
    | Deref ((_, _), e) -> fprintf pf "*%a" ppPrintExpression e 
    | StructRead ((_, _), e, s) -> fprintf pf "%a.%s" ppPrintExpression e s
    | ArrayRead ((_, _),e1, e2) -> fprintf pf "%a[%a]" ppPrintExpression e1 ppPrintExpression e2
    | Literal ((_, _),l) -> fprintf pf "%a" PpCommon.pp_literal l 
    | UnOp ((_, _), o, e) -> fprintf pf "%a %a" pp_unop o ppPrintExpression e
    | BinOp ((_, _), o, e1, e2) -> fprintf pf "%a %a %a" ppPrintExpression e1 pp_binop o ppPrintExpression e2
    | Ref ((_, _),true,e) -> fprintf pf "&mut %a" ppPrintExpression e 
    | Ref ((_, _),false,e) -> fprintf pf "&%a" ppPrintExpression e 
    | ArrayStatic ((_, _),el) ->  
      Format.fprintf pf "[%a]"
        (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    |StructAlloc  ((_, _), id, m) ->
      let pp_field pf (x, y) = Format.fprintf pf "%s:%a" x ppPrintExpression y in
      Format.fprintf pf "%s{%a}" id
        (Format.pp_print_list ~pp_sep:pp_comma pp_field)
        (Common.TypesCommon.FieldMap.bindings m)
    | EnumAlloc ((_, _),id,el) ->  
      Format.fprintf pf "[%s(%a)]" id
        (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    | MethodCall ((_, _), _id, _el) -> 
      failwith "method call should not occur in mir expressions"

let ppPrintDeclaration (pf : Format.formatter) (d : declaration) : unit = 
  if d.mut then
    fprintf pf "let mut %s : %a;" d.id pp_type d.varType 
  else fprintf pf "let %s : %a;" d.id pp_type d.varType

let ppPrintAssignement (pf : Format.formatter) (a : assignment) : unit = 
  fprintf pf "%a = %a;" ppPrintExpression a.target ppPrintExpression a.expression

let ppPrintTerminator (pf : Format.formatter) (t : terminator) : unit = 
  match t with 
    | Goto lbl -> fprintf pf "goto %d;" lbl 
    | Invoke {id; params;next} -> fprintf pf "%s(%a) -> %d" id (Format.pp_print_list ~pp_sep:pp_comma ppPrintExpression) params next
    | Return None -> fprintf pf "return;"
    | Return (Some e) ->  fprintf pf "return %a;" ppPrintExpression e 
    | SwitchInt (e, cases, default) -> 
      let pp_case pf (x, y) = Format.fprintf pf "%d:%d" x y in
        fprintf pf "switchInt(%a) [%a, otherwise: %d]" 
          ppPrintExpression e 
          (Format.pp_print_list ~pp_sep:pp_comma pp_case) cases
          default
  
let ppPrintBasicBlock (pf : Format.formatter) (lbl : label) (bb : basicBlock) : unit = 
  let pp_block pf bb = 
    match bb.terminator with 
    None -> failwith "blocks must have a terminator"
    |Some t ->
    fprintf pf "%a;%a" (Format.pp_print_list ~pp_sep:pp_semi ppPrintAssignement) bb.assignments ppPrintTerminator t in
  fprintf pf "bb%d{%a}" lbl pp_block bb

(* let rec successors *)

(* termination *)
let ppPrintCfg (pf : Format.formatter) (cfg : cfg) : unit = 
  let check = ref [] in
  let rec aux (lbl : label)  =
    if List.mem lbl !check then () else 
    let _ = check := lbl::!check in
    let bb = BlockMap.find lbl cfg.blocks in
    let _ = ppPrintBasicBlock pf lbl bb in
    match bb.terminator with 
      | None -> failwith "blocks must have a terminator"
      | Some t -> match t with
        | Goto lbl -> aux lbl
        | Invoke i -> aux i.next
        | Return _ -> ()
       | SwitchInt (_, cases, default) -> 
          let _ = List.iter aux (List.map snd cases) in 
          aux default
  in aux cfg.input

let ppPrintMethodSig (pf : Format.formatter) (s : Common.TypesCommon.method_sig) : unit = 
  match s.rtype with 
  None ->
    fprintf pf "(%a)" (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params
| Some t -> 
    fprintf pf "(%a) -> %a" (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params pp_type t

let ppPrintMethod (pf : Format.formatter) (m: (declaration list * cfg) Common.TypesCommon.method_defn) : unit = 
  fprintf pf  "method %a %a %a" ppPrintMethodSig m.m_proto (pp_print_list ~pp_sep:pp_comma ppPrintDeclaration) (fst m.m_body) ppPrintCfg (snd m.m_body)

let ppPrintProcess (pf : Format.formatter) (p : (declaration list * cfg) Common.TypesCommon.process_defn) : unit = 
  fprintf pf  "%a %a" (pp_print_list ~pp_sep:pp_comma ppPrintDeclaration) (fst p.p_body) ppPrintCfg (snd p.p_body)


let ppPrintModule (pf : Format.formatter) (m : (declaration list * cfg) Common.TypesCommon.sailModule ) : unit = 
  fprintf pf "module %a %d" (pp_print_list ~pp_sep:pp_comma ppPrintMethod) m.methods (List.length m.methods)
