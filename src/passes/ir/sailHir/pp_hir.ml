open Common
open PpCommon
open Format
open AstHir
open Hir


let rec ppPrintExpression (pf : Format.formatter) (e : expression) : unit =
  let open Format in 
  match e.exp with 
    | Variable s -> fprintf pf "%s" s
    | Deref e -> fprintf pf "*%a" ppPrintExpression e 
    | StructRead (_,e, (_,s)) -> fprintf pf "%a.%s" ppPrintExpression e s
    | ArrayRead (e1, e2) -> fprintf pf "%a[%a]" ppPrintExpression e1 ppPrintExpression e2
    | Literal (l) -> fprintf pf "%a" PpCommon.pp_literal l 
    | UnOp (o, e) -> fprintf pf "%a %a" pp_unop o ppPrintExpression e
    | BinOp ( o, e1, e2) -> fprintf pf "%a %a %a" ppPrintExpression e1 pp_binop o ppPrintExpression e2
    | Ref (true,e) -> fprintf pf "&mut %a" ppPrintExpression e 
    | Ref (false,e) -> fprintf pf "&%a" ppPrintExpression e 
    | ArrayStatic el ->  
      fprintf pf "[%a]"
        (pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    |StructAlloc  (_,id, m) ->
      let pp_field pf (x, y) = fprintf pf "%s:%a" x ppPrintExpression y in
      fprintf pf "%s{%a}" (snd id)
        (pp_print_list ~pp_sep:pp_comma pp_field)
        m
    | EnumAlloc (id,el) ->  
      fprintf pf "[%s(%a)]" (snd id)
        (pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    | MethodCall _ -> ()

let rec ppPrintStatement (pf : Format.formatter) (s : statement) : unit = match s.stmt with
| DeclVar (_mut, id, _opt_t,_opt_exp) -> fprintf pf "\nvar %s;" id 
| Assign(e1, e2) -> fprintf pf "\n%a = %a;" ppPrintExpression e1 ppPrintExpression e2
| Seq(c1, c2) -> fprintf pf "%a%a" ppPrintStatement c1 ppPrintStatement c2
| If(cond_exp, then_s,else_s) -> fprintf pf "\nif (%a) {\n%a\n}\n%a" 
  ppPrintExpression cond_exp 
  ppPrintStatement then_s
  (pp_print_option (fun pf -> fprintf pf "else {%a\n}" ppPrintStatement)) else_s
| Loop c -> fprintf pf "\nloop {%a\n}" ppPrintStatement c
| Break -> fprintf pf "break;"
| Case(_e, _cases) -> ()
| Invoke (var, _mod_loc, (_,id), el) -> fprintf pf "\n%a%s(%a);" (pp_print_option  pp_print_string) var id (pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
| Return _e -> fprintf pf "\nreturn ?;"
| Block c -> fprintf pf "\n{\n@[ %a @]\n}" ppPrintStatement c
| Skip -> ()

let ppPrintMethodSig (pf : Format.formatter) (s : TypesCommon.method_sig) : unit = 
  match s.rtype with 
  None ->
    fprintf pf "%s(%a)" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params
| Some t -> 
    fprintf pf "%s(%a) -> %a" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params pp_type t

let ppPrintMethod (pf : Format.formatter) (m: statement TypesCommon.method_defn) : unit = 
  match m.m_body with
  | Right s ->  fprintf pf  "fn %a{\n@{<hov 2> @ %a@]}\n"  ppPrintMethodSig m.m_proto ppPrintStatement s
  | Left _ -> fprintf pf "extern fn %a\n" ppPrintMethodSig m.m_proto


(* let ppPrintProcess (pf : Format.formatter) (p : (declaration list * cfg) Common.TypesCommon.process_defn) : unit = 
  fprintf pf  "proc %s() {\n%a\n%a}\n" p.p_name (pp_print_list ~pp_sep:pp_semicr ppPrintDeclaration) (fst p.p_body) ppPrintCfg (snd p.p_body) *)


let ppPrintModule (pf : Format.formatter) (m : Pass.out_body SailModule.t ) : unit = 
  fprintf pf "// Sail HIR Representation: %s\n%a" m.md.name 
  (pp_print_list ppPrintMethod) m.body.methods
  (* (pp_print_list ~pp_sep:pp_comma ppPrintProcess) m.body.processes *)