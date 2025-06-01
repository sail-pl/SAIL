open TypesCommon
let register_builtin name generics p rtype variadic l: method_sig list = 
  let params = List.mapi (fun i ty -> {loc=dummy_pos; id=Printf.sprintf "p%i" i; mut=true;ty}) p in 
  {pos=dummy_pos; variadic; name; generics;rtype;params;extern=false}::l

let get_builtins () : method_sig list = 
  []
  |> register_builtin "box" ["T"] [mk_locatable dummy_pos (GenericType "T")] (Some (mk_locatable dummy_pos (Box (mk_locatable dummy_pos (GenericType "T"))))) false