open Common
open PpCommon
open Format
open Ast
open TypesCommon

let rec ppPrintExpression (pf : Format.formatter) (e : _) : unit = 
  let open Format in 
  match e.node with 
    | Variable s -> fprintf pf "%s" s
    | Deref e -> fprintf pf "*%a" ppPrintExpression e
    | StructRead st -> fprintf pf "%a.%s" ppPrintExpression st.value.strct st.value.field.value  
    | ArrayRead ar -> fprintf pf "%a[%a]" ppPrintExpression ar.array ppPrintExpression ar.idx
    | Literal (l) -> fprintf pf "%a" PpCommon.pp_literal l 
    | UnOp (o, e) -> fprintf pf "%a %a" pp_unop o ppPrintExpression e
    | BinOp bop -> fprintf pf "%a %a %a" ppPrintExpression bop.left pp_binop bop.op ppPrintExpression bop.right
    | Ref (true,e) -> fprintf pf "&mut %a" ppPrintExpression e 
    | Ref (false,e) -> fprintf pf "&%a" ppPrintExpression e 
    | ArrayStatic el ->  
      fprintf pf "[%a]"
        (pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    | StructAlloc  st  ->
      let pp_field pf (x, (y: _ locatable)) = fprintf pf "%s:%a" x ppPrintExpression y.value in
      fprintf pf "%s{%a}" st.value.name.value
        (pp_print_list ~pp_sep:pp_comma pp_field)
        st.value.fields
    | EnumAlloc (id,el) ->  
      fprintf pf "[%s(%a)]" id.value
        (pp_print_list ~pp_sep:pp_comma ppPrintExpression) el
    | MethodCall m -> 
      fprintf pf "%a%s(%a)" 
      (pp_print_option  (fun fmt ml -> fprintf fmt "%s::" ml.value)) m.import
      m.value.id.value
      (pp_print_list ~pp_sep:pp_comma ppPrintExpression) m.value.args 

let rec ppPrintStatement (pf : Format.formatter) (s : _) : unit = match s.node with
| DeclVar d  -> fprintf pf "\nvar %s%a%a;" d.id 
      (pp_print_option (fun fmt -> fprintf fmt " : %a" pp_type)) d.ty
      (pp_print_option (fun fmt -> fprintf fmt " = %a" ppPrintExpression)) d.value

| Assign a -> fprintf pf "\n%a = %a;" ppPrintExpression a.path ppPrintExpression a.value
| Seq(c1, c2) -> fprintf pf "%a%a" ppPrintStatement c1 ppPrintStatement c2
| If if_ -> fprintf pf "\nif (%a) {\n%a\n}\n%a" 
  ppPrintExpression if_.cond 
  ppPrintStatement if_.then_
  (pp_print_option (fun pf -> fprintf pf "else {%a\n}" ppPrintStatement)) if_.else_
| Loop c -> fprintf pf "\nloop {%a\n}" ppPrintStatement c
| Break -> fprintf pf "break;"
| Case _ -> ()
| Invoke i -> fprintf pf "\n%a%a%s(%a);" 
    (pp_print_option  (fun fmt v -> fprintf fmt "%s = " v)) i.value.ret_var
    (pp_print_option  (fun fmt ml -> fprintf fmt "%s::" ml.value)) i.import
    i.value.id.value
    (pp_print_list ~pp_sep:pp_comma ppPrintExpression) i.value.args
| Return e -> fprintf pf "\nreturn %a;" (pp_print_option  ppPrintExpression) e
| Block c -> fprintf pf "\n{\n@[ %a @]\n}" ppPrintStatement c
| Skip -> ()

let ppPrintMethodSig (pf : Format.formatter) (s : TypesCommon.method_sig) : unit = 
  match s.rtype with 
  None ->
    fprintf pf "%s(%a)" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params
| Some t -> 
    fprintf pf "%s(%a) -> %a" s.name (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) s.params pp_type t

let ppPrintMethod (pf : Format.formatter) (m: _ TypesCommon.method_defn) : unit = 
  match m.m_body with
  | Right s ->  fprintf pf  "fn %a{\n@[<hov 2>%a@]\n}\n"  ppPrintMethodSig m.m_proto ppPrintStatement s
  | Left _ -> fprintf pf "extern fn %a\n" ppPrintMethodSig m.m_proto


(* let ppPrintProcess (pf : Format.formatter) (p : (declaration list * cfg) Common.TypesCommon.process_defn) : unit = 
  fprintf pf  "proc %s() {\n%a\n%a}\n" p.p_name (pp_print_list ~pp_sep:pp_semicr ppPrintDeclaration) (fst p.p_body) ppPrintCfg (snd p.p_body) *)
