type sailtype =
  | Bool 
  | Int 
  | Float 
  | Char 
  | String
  | ArrayType of sailtype
  | CompoundType of string * sailtype list
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

(* expressions are control free *)
type expression = 
    Variable of string
  | Literal of literal
  | UnOp of unOp * expression
  | BinOp of binOp * expression * expression
  | Ref of expression
  | Deref of expression
  | ArrayRead of expression * expression
  | ArrayStatic of expression list
  | StructRead of expression * string
  | StructAlloc of (string * expression) list
  | EnumAlloc of (string * expression list) 
  | MethodCall of string * expression list
      
type lhs = 
    LHSVar of string 
  | LHSField of lhs * string 
  | LHSArray of lhs * expression

type declaration =
  | VariableDeclaration of string * sailtype * expression
  | SignalDeclaration of string

type pattern =
  | PVar of string
  | PCons of string * pattern list 

type statement =
  | Declaration of declaration
  | Assign of lhs * expression
  | Seq of statement list
  | Par of statement list
  | If of expression * statement * statement option
  | While of expression * statement
  | Case of expression * (pattern * statement) list
  | Invoke of string option * string * expression list
  | Return of expression option
  | Run of string * expression list
  | Loop of statement
  | Emit of string
  | Await of string
  | Watching of string * statement

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

type method_defn =  
  {
    m_name : string; 
    m_generics : string list;
    m_params : (string * sailtype) list;
    m_rtype : sailtype option;
    m_body : statement
  }

type process_defn = 
  {
    p_name : string;
    p_generics : string list;
    p_interface : (string * sailtype) list * string list;
    p_body : statement
  }

type program =
  {
    structs : struct_defn list;
    enums : enum_defn list;
    methods : method_defn list ;
    processes : process_defn list
  }

(* to sort definitions *)

type defn =
  | Struct of struct_defn
  | Enum of enum_defn
  | Method of method_defn
  | Process of process_defn

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


  
