open Llvm

type sailor_values = 
  | Ground of llvalue 
  | Array of (llvalue * int)

type composite_type = (string * int) list



Global of | Scoped of 


Enum of string 