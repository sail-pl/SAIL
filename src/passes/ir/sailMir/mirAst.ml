open Common
open TypesCommon
open IrThir

(*
type unOp = Not | Neg
type binOp = Add | Sub | Mul | Div

type constant = literal (* nothing else for now *)

type ('info,'import) lvalue = 
  | UserBinding of string 
  | TempBinding of string
  | FunArg of string
  | FunRet of string
  | Projection of {import : 'import ; strct : ('info,'import) lvalue ; field : l_str}
  | Deref of ('info,'import) lvalue
  | ArrayIndex of {array : ('info,'import) lvalue; index : ('info,'import) lvalue}


type ('info,'import) rvalue = 
  | Use of ('info,'import) lvalue
  | BinOp of {left : ('info,'import) lvalue ; right : ('info,'import) lvalue; op : binOp}
  | UnOp of unOp * ('info,'import) lvalue
  | Box
  | Constant of constant
  | Aggregate of ('info, 'import) lvalue dict

type drop_kind = Shallow | Deep 
type statement = Assign of lvalue * rvalue | Drop of drop_kind * lvalue

*)

type expression = ThirUtils.expression
type statement = ThirUtils.statement 

type declaration = {location : loc; mut : bool; id : string; varType : sailtype}
type assignment = {location : loc; target : expression; expression : expression}

type label = int
module LabelSet = Set.Make(Int)

type terminator = 
| Goto of label
| Invoke of {id : string; origin:l_str; target: string option; params : expression list; next:label}
| Return of expression option
| SwitchInt of {choice : expression ; paths : (int * label) list ; default : label}
| Break 


module V : Common.Env.Variable with type t = param = 
  struct 

  type t = param
  let string_of_var (v:t) = Printf.sprintf "{ty:%s}" (string_of_sailtype (Some v.ty))

  let param_to_var = Fun.id
end

module VE = Common.Env.VariableEnv(V)

type ('f,'b) basicBlock = {
  forward_info : 'f;
  backward_info : 'b;
  assignments : assignment list;
  predecessors : LabelSet.t;
  terminator : terminator option;
  location : loc;
}

module BlockMap = Map.Make(Int)

(* A CFG is well formed if 
  - input and output are defined in blocks
  - any terminator points to a block inside blocks *)

type cfg = {
  input : label;
  output : label;
  blocks : (VE.t,unit) basicBlock BlockMap.t
}

type mir_function = declaration list * cfg