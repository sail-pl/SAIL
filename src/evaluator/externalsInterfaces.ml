open Common.TypesCommon
open Common.SailModule

let e_print_string = {pos= dummy_pos;name="print_string"; generics=[];params=[("x", false, String)];variadic=false;rtype=None}
let e_print_int = {pos= dummy_pos;name="print_int"; generics=[];params=[("x", false, Int)];variadic=false;rtype=None}

let e_print_new_line = {pos= dummy_pos;name="print_newline"; generics=[];params=[];variadic=false;rtype=None}

let drop = {pos=dummy_pos;name="drop"; generics=["A"]; params=[("x", false, Box (GenericType "A"))];variadic=false;rtype=None}
let exSig = {
  name = "_External"; 
  declEnv = DeclEnv.empty;
  methods = [];
  processes = [];
}