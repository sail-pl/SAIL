type datatype =
    Int 
  | Float 
  | Bool 
  | Char 
  | String
  | Array of datatype * int
  | Ref of bool * datatype
  | Void
  | Compound of string * datatype list
  | Generic of string

type litteral =
  | LInt of int
  | LFLoat of float
  | LBool of bool
  | LChar of char
  | LString of string

type unop = Neg | Not
type binop = Plus | Mult | Div | Minus | Rem
           | Lt | Le | Gt | Ge | Eq | NEq | And | Or

      
type expression =
    Var of string
  | Lit of litteral
  | Decl of declaration
  | Assign of expression * expression
  | Deref of bool * expression
  | ADeref of expression * expression
  | ACreateInit of expression list
  | ACreate of datatype * expression
  | SDeref of expression * string
  | SCreate of (string * expression) list
  | Unop of unop * expression
  | Binop of binop * expression * expression
  | Return of expression option
  | If of expression * block_expression * block_expression option
  | While of expression * block_expression
and declaration =
    DeclVar of bool * string * datatype * expression
  | DeclSig of string
and block_expression = expression list
and case = string * string list * expression
           
type behavior = 
  | Emit of expression
  | When of expression * behavior
  | Watch of expression * behavior
  | Spawn of string * expression list

type struct_defn = 
  {  
    s_name : string;
    s_generics : string list;
    s_fields : (string * datatype) list;
  }

type enum_defn = 
{
  e_name : string;
  e_generics : string list;
  e_injections :  (string * datatype) list;
}

type signature = 
  {
    params : (string * datatype) list; 
    rtype : datatype option;
  } 

type method_defn =  
  {
    m_name : string; 
    m_signature : signature;
    m_body : block_expression
  }

type process_defn = 
  {
    p_name : string;
    p_signature : signature;
    p_body : behavior
  }

type defn =
  | Struct of struct_defn
  | Enum of enum_defn
  | Method of method_defn
  | Process of process_defn

type program =
  {
    structs : struct_defn list;
    enums : enum_defn list;
    methods : method_defn list ;
    processes : process_defn list
  }


let mk_program l =
  let rec aux l =
    match l with
      [] -> ([],[],[],[])
    | d::l ->
      let (s,e,m,p) = aux l in
        match d with
          | Struct d -> (d::s,e,m,p)
          | Enum d -> (s,d::e,m,p)
          | Method d -> (s,e,d::m,p)
          | Process d -> (s,e, m,d::p)
  in 
  let (s,e,m,p) = aux l in 
    {structs = s; enums =e; methods=m; processes=p}


  
