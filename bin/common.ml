open Format

type sailtype =
  | Bool 
  | Int 
  | Float 
  | Char 
  | String
  | ArrayType of sailtype
  | CompoundType of string * sailtype list
  | Box of sailtype
  | RefType of sailtype * bool
  | GenericType of string

type literal =
  | LBool of bool
  | LInt of int
  | LFloat of float
  | LChar of char
  | LString of string

type unOp = Neg | Not

type binOp = Plus | Mul | Div | Minus | Rem
           | Lt | Le | Gt | Ge | Eq | NEq | And | Or

type pattern =
  | PVar of string
  | PCons of string * pattern list 

  type struct_defn = 
  {  
    s_name : string;
    s_generics : string list;
    s_fields : (string * sailtype) list;
  }

type enum_defn = 
{
  e_name : string;
  e_generics : string list;
  e_injections :  (string * sailtype list) list;
}

type 'a process_defn = 
  {
    p_name : string;
    p_generics : string list;
    p_interface : (string * sailtype) list * string list;
    p_body : 'a
  }

type 'a method_defn =  
  {
    m_name : string; 
    m_generics : string list;
    m_params : (string * sailtype) list;
    m_rtype : sailtype option;
    m_body : 'a
  }

  type 'a program =
  {
    structs : struct_defn list;
    enums : enum_defn list;
    methods : 'a method_defn list ;
    processes : 'a process_defn list
  }

  let pp_comma (pf : formatter) (() : unit) : unit = Format.fprintf pf "," 
  let pp_field (pp_a : formatter -> 'a -> unit) (pf : formatter) ((x,y) : string * 'a) = 
    Format.fprintf pf "%s:%a" x pp_a y

    
let string_of_unop u = match u with Neg -> "-" | Not -> "~"

let string_of_binop b = match b with 
  | Plus -> "+" 
  | Mul -> "*"
  | Div -> "/"
  | Minus -> "-"
  | Rem -> "%"
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Eq -> "=="
  | NEq -> "!="
  | And -> "&&"
  | Or -> "||"

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
      | ArrayType t -> Format.fprintf pf "array<%a>" pp_type t
      | CompoundType (x, tl) -> 
          Format.fprintf pf "%s<%a>" x (pp_print_list ~pp_sep:pp_comma pp_type) tl
      | Box(t) -> Format.fprintf pf "ref<%a>" pp_type t
      | RefType (t,b) -> 
          if b then Format.fprintf pf "&mut %a" pp_type t
          else Format.fprintf pf "& %a" pp_type t
      | GenericType(s) -> pp_print_string pf s 

let pp_method (pp_a : formatter -> 'a -> unit ) (pf : formatter) (m : 'a method_defn) =
  match m.m_rtype with 
  None -> 
    fprintf pf "method %s (%a) {\n%a\n}\n" 
      m.m_name 
      (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) m.m_params 
      pp_a m.m_body
  | Some t -> 
    fprintf pf "method %s (%a):%a {\n%a\n}\n" 
      m.m_name 
      (pp_print_list ~pp_sep:pp_comma (pp_field pp_type)) m.m_params 
      pp_type t
      pp_a m.m_body

let pp_process (pp_a : formatter -> 'a -> unit) (pf : formatter) (p : 'a process_defn) =
  fprintf pf "%a\n" pp_a p.p_body 

let pp_program (pp_a : formatter -> 'a -> unit) ((pf : formatter) : formatter) (p : 'a program) = 
  List.iter (pp_method pp_a pf) p.methods;
  List.iter (pp_process pp_a pf) p.processes
      