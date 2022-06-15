open Common.TypesCommon

let e_print_string = {pos= Lexing.dummy_pos;name="print_string"; generics=[];params=[("x", String)];rtype=None}
let e_print_int = {pos= Lexing.dummy_pos;name="print_int"; generics=[];params=[("x", Int)];rtype=None}

let e_print_new_line = {pos= Lexing.dummy_pos;name="print_newline"; generics=[];params=[];rtype=None}

let drop = {pos= Lexing.dummy_pos;name="drop"; generics=["A"]; params=[("x",Box (GenericType "A"))];rtype=None}
let exSig = {
  name = "_External"; 
  structs = [];
  enums =[];
  methods = [];
  processes = [];
  ffi = [e_print_string; e_print_new_line; e_print_new_line];
}