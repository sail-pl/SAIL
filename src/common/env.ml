open TypesCommon

module type Declarations = sig
  type process_decl
  type method_decl
  type struct_decl
  type enum_decl
end


module type DeclEnvType = functor (D : Declarations) -> sig
  open D

  type t 
  val empty : t
  val add_process : t -> string -> process_decl -> t
  val add_method : t -> string -> method_decl -> t
  val add_struct : t -> string -> struct_decl -> t
  val add_enum : t -> string -> enum_decl -> t
  val find_process : t -> string -> process_decl option
  val find_method : t -> string -> method_decl option
  val find_struct : t -> string -> struct_decl option
  val find_enum : t -> string -> enum_decl option
  val write_declarations : 'a -> 'b -> unit
  val print_declarations : t -> unit
  val iter_methods : (string -> method_decl -> unit) -> t -> unit
end


module DeclarationsEnv (D:Declarations)  = struct
  open D

  type t = {
    methods : method_decl FieldMap.t;
    processes : process_decl FieldMap.t;
    structs : struct_decl FieldMap.t;
    enums : enum_decl FieldMap.t;
  } 

  let empty = {
    methods = FieldMap.empty;
    processes = FieldMap.empty;
    structs = FieldMap.empty;
    enums = FieldMap.empty;
  }

  let add_process decls id (p:process_decl) = { decls with processes=(FieldMap.add id p decls.processes)}
  let add_method decls id (m:method_decl) = { decls with methods=(FieldMap.add id m decls.methods)}
  let add_struct decls id (s:struct_decl) = { decls with structs=(FieldMap.add id s decls.structs)}
  let add_enum decls id (e:enum_decl) = { decls with enums=(FieldMap.add id e decls.enums)}



  let find_process decls id = FieldMap.find_opt id decls.processes 
  let find_method decls id = FieldMap.find_opt id decls.methods 
  let find_struct decls id = FieldMap.find_opt id decls.structs 
  let find_enum decls id = FieldMap.find_opt id decls.enums 

  let write_declarations _decls _filename = () (* todo *) 

  let iter_methods f env = FieldMap.iter f env.methods


  let print_declarations decls = 
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "process %s\n" n) decls.processes;
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "method %s\n" n) decls.methods;
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "struct %s\n" n) decls.structs;
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "enum %s\n" n) decls.enums

end


module type Variable = sig
  type t
  val string_of_var : t -> string

  val to_var : bool -> sailtype -> t 
end
 

module VariableDeclEnv = functor (D:Declarations) (V:Variable) -> struct
  module D = DeclarationsEnv(D)
  
  type variable = V.t
  type frame = variable FieldMap.t
  type t = frame list * D.t

  let empty g : t = 
    let c = FieldMap.empty in [c],g

  let push_frame (env,g) s = 
    s :: env, g

  let pop_frame (env,g) = 
    List.tl env, g

  let new_frame e =
    let c = FieldMap.empty in
    push_frame e c

  let current_frame = function [],_ -> failwith "environnement is empty !" | (h::t),g ->  h,(t,g)

  
  let print_env (e:t) =
    let rec aux (env:t) : string = 
      let c,env = current_frame env in
      let p =
        FieldMap.fold 
          (fun n v -> let s = Printf.sprintf "(%s:%s) " n (V.string_of_var v) in fun n  ->  s ^ n) c "]"
      in let c = "\t[ " ^ p  in
      match env with
      | [],_ -> c ^ "\n"
      | _ -> c ^ "\n"  ^ aux env
    in 
    try
    Printf.sprintf "env : \n{\n %s }" (aux e)
    with _ -> failwith "problem with printing env (env empty?)"
  

  let get_process (_,g) name = D.find_process g name
  let get_method (_,g) name = D.find_method g name
  let get_struct (_,g) name = D.find_struct g name
  let get_enum (_,g) name = D.find_enum g name

    
  let get_var e name  = 
    let rec aux env = 
      let current,env = current_frame env in
      match FieldMap.find_opt name current with 
      | Some v -> Result.ok v
      | None  when fst env = [] ->  Result.error [dummy_pos,Printf.sprintf "variable %s doesn't exist !" name]
      | _ -> aux env
      in aux e

  let declare_var (e:t) name (l:loc) (v:variable) =
    let current,_env = current_frame e in
    match FieldMap.find_opt name current with 
    | Some _ -> Result.error [l,Printf.sprintf "variable %s already exists !" name]
    | None -> 
      let upd_frame = FieldMap.add name v current in
      push_frame _env upd_frame |> Result.ok


  let get_start_env decls args =
    let env = empty decls |> new_frame in
    List.fold_left (fun m (n,mut,t) ->
      try 
      declare_var m n dummy_pos (V.to_var mut t) |> Result.get_ok (* there should not be any error*)
      with Invalid_argument _ -> failwith "declare_var error"
    ) env
    args
end
