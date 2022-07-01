open IrThir

type statement = 
| DeclVar of Common.TypesCommon.loc * bool * string * Common.TypesCommon.sailtype option
| Assign of Common.TypesCommon.loc * Thir.expression * Thir.expression

type label = int

type terminator = 
| Goto of label
| Invoke of {id : string; params : Thir.expression list; next:label}
| Return of Thir.expression option
| SwitchInt of Thir.expression * (int * label) list * label


type basicBlock = {
  statements : statement list;
  terminator : terminator option
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