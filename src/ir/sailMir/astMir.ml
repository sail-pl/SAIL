type expression = IrThir.Thir.expression

type declaration = {location : Common.TypesCommon.loc; mut : bool; id : string; varType : Common.TypesCommon.sailtype}
type assignment = {location : Common.TypesCommon.loc; target : expression; expression : expression}

type label = int

type terminator = 
| Goto of label
| Invoke of {id : string; params : expression list; next:label}
| Return of expression option
| SwitchInt of expression * (int * label) list * label

type basicBlock = {
  assignments : assignment list;
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
