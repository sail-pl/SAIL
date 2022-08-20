open Common.TypesCommon

type expression = IrThir.Thir.expression
type statement = IrThir.Thir.statement

type declaration = {location : loc; mut : bool; id : string; varType : sailtype}
type assignment = {location : loc; target : expression; expression : expression}

type label = int

type terminator = 
| Goto of label
| Invoke of {id : string; target: string option; params : expression list; next:label}
| Return of expression option
| SwitchInt of expression * (int * label) list * label


type vtype = {
    ty:sailtype;
    mut:bool;
    is_init:bool;
    is_used:bool;
}

module V : Common.Env.Variable with type t = vtype = 
  struct 

  type t = vtype
  let string_of_var v = Printf.sprintf "{ty:%s;init:%b;used:%b}" (string_of_sailtype (Some v.ty)) v.is_init v.is_used

  let to_var mut ty = {ty;mut;is_init=true;is_used=false}
end

module VE = Common.Env.VariableEnv(V)

type basicBlock = {
  env : VE.t;
  assignments : assignment list;
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
