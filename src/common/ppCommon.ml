open Format
open TypesCommon




let pp_comma (pf : formatter) (() : unit) : unit = Format.fprintf pf "," 

let pp_semi (pf : formatter) (() : unit) : unit = Format.fprintf pf ";" 

let pp_semicr (pf : formatter) (() : unit) : unit = Format.fprintf pf ";\n" 

let pp_field (pp_a : formatter -> 'a -> unit) (pf : formatter) (p : param) = 
  Format.fprintf pf "%s:%s%a" (if p.mut then "mut " else "") p.id pp_a p.ty
(*
let rec pp_pattern pf p = 
  match p with 
    | PVar x -> Format.pp_print_string pf x
    | PCons (c, pl) -> Format.fprintf pf "%s(%a)" c (Format.pp_print_list ~pp_sep:pp_comma pp_pattern) pl
*)    
let pp_unop pf u =
  let u = match u with Neg -> "-" | Not -> "~" in
  Format.pp_print_string pf  u 

let pp_binop pf b = 
  let b = 
    match b with 
    | Plus -> "+" | Mul -> "*" | Div -> "/" | Minus -> "-" | Rem -> "%"
    | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">=" | Eq -> "==" | NEq -> "!="
    | And -> "&&" | Or -> "||"
  in Format.pp_print_string pf b

  let pp_literal (pf : formatter) (c : literal) : unit = 
    match c with 
    | LBool (b) -> Format.fprintf pf "%b" b
    | LInt (i) -> pp_print_int pf i
    | LFloat (f) -> Format.fprintf pf "%f" f
    | LChar (c) -> Format.fprintf pf "\'%c\'" c
    | LString s -> Format.fprintf pf "\"%s\"" s 
  
  

  let rec pp_type (pf : formatter) (t : sailtype) : unit =
    match t with 
        Bool -> pp_print_string pf "bool"
      | Int -> pp_print_string pf "int"
      | Float -> pp_print_string pf "float"
      | Char -> pp_print_string pf "char"
      | String -> pp_print_string pf "string"
      | ArrayType (t,s) -> Format.fprintf pf "array<%a;%d>" pp_type t s
      | CompoundType (x, tl) -> 
          Format.fprintf pf "%s<%a>" x (pp_print_list ~pp_sep:pp_comma pp_type) tl
      | Box(t) -> Format.fprintf pf "ref<%a>" pp_type t
      | RefType (t,b) -> 
          if b then Format.fprintf pf "&mut %a" pp_type t
          else Format.fprintf pf "& %a" pp_type t
      | GenericType(s) -> pp_print_string pf s 

let pp_method (pp_method_body : int -> formatter -> (tag option, 'a) Either.t -> unit ) (pf : formatter) (m : 'a method_defn) =
  match m.m_proto.rtype with 
  None -> 
    fprintf pf "method %s (%a) {\n%a\n}\n" 
      m.m_proto.name 
      (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) m.m_proto.params 
      (pp_method_body 1) m.m_body
  | Some t -> 
    fprintf pf "method %s (%a):%a {\n%a\n}\n" 
      m.m_proto.name 
      (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) m.m_proto.params 
      pp_type t
      (pp_method_body 1) m.m_body

let pp_process (pp_process_body : int -> formatter -> 'a -> unit) (pf : formatter) (p : 'a process_defn) =
  fprintf pf "process %s (-) {\n%a\n}\n" p.p_name 
  (pp_process_body 1) p.p_body 

let pp_program (pp_method_body : int -> formatter -> (tag option, 'a) Either.t -> unit) 
(pp_process_body : int -> formatter -> 'a -> unit)
((pf : formatter) : formatter) (p : 'a SailModule.t) = 
  List.iter (pp_method pp_method_body pf) p.methods;
  List.iter (pp_process pp_process_body pf) p.processes
      