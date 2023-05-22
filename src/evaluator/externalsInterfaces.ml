open Common.TypesCommon
open Common.SailModule

let e_print_string = {pos= dummy_pos;name="print_string"; generics=[];params=[{id="x";mut=false;ty=String; loc=dummy_pos}];variadic=false;rtype=None}
let e_print_int = {pos= dummy_pos;name="print_int"; generics=[];params=[{id="x";mut=false;ty=Int; loc=dummy_pos}];variadic=false;rtype=None}

let e_print_new_line = {pos= dummy_pos;name="print_newline"; generics=[];params=[];variadic=false;rtype=None}

let drop = {pos=dummy_pos;name="drop"; generics=["A"]; params=[{id="x";mut=false;ty=Box (GenericType "A"); loc=dummy_pos}];variadic=false;rtype=None}
let exSig = {
  declEnv = DeclEnv.empty;
  methods = [];
  processes = [];
  builtins=[];
  imports=ImportSet.empty;
  md = {name="_External"; hash= ""; libs=FieldSet.empty}
}