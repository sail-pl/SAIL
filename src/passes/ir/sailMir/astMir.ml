open Common
open TypesCommon
open IrThir

type expression = Thir.expression
type statement = Thir.statement

type declaration = {location : loc; mut : bool; id : string; varType : sailtype}
type assignment = {location : loc; target : expression; expression : expression}

type label = int
module LabelSet = Set.Make(Int)

type terminator = 
| Goto of label
| Invoke of {id : string; origin:l_str; target: string option; params : expression list; next:label}
| Return of expression option
| SwitchInt of expression * (int * label) list * label
| Break 


module V : Common.Env.Variable with type t = param = 
  struct 

  type t = param
  let string_of_var (v:t) = Printf.sprintf "{ty:%s}" (string_of_sailtype (Some v.ty))

  let param_to_var = Fun.id
end

module VE = Common.Env.VariableEnv(V)

type basicBlock = {
  env : VE.t;
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
  blocks : basicBlock BlockMap.t
}

type mir_function = declaration list * cfg
