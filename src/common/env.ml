open TypesCommon

module type Declarations = sig
  type process_decl
  type method_decl
  type struct_decl
  type enum_decl
end


module type DeclEnvType = sig
  type t
  type ('a, 'b, 'c, 'd) ty = Process of 'a | Method of 'b | Struct of 'c | Enum of 'd
  type decl
  type decl_ty

  val empty : t
  val add_declaration : t -> string -> decl -> t
  val find_declaration : t -> decl_ty -> decl option
  val write_declarations : t -> string -> unit
end


module DeclarationsEnv (D:Declarations) = struct
  type t = {
    methods : D.method_decl FieldMap.t;
    processes : D.process_decl FieldMap.t;
    structs : D.struct_decl FieldMap.t;
    enums : D.enum_decl FieldMap.t;
  } 

  type ('a, 'b, 'c, 'd) ty = Process of 'a | Method of 'b | Struct of 'c | Enum of 'd
  type decl = (D.process_decl, D.method_decl, D.struct_decl, D.enum_decl) ty
  type decl_ty = (string,string,string,string) ty


  let empty = {
    methods = FieldMap.empty;
    processes = FieldMap.empty;
    structs = FieldMap.empty;
    enums = FieldMap.empty;
  }

  let add_declaration decls id (d:decl) = match d with
  (* todo : check name conflict *)
  | Process p -> { decls with processes=(FieldMap.add id p decls.processes)}
  | Method m -> { decls with methods=(FieldMap.add id m decls.methods)}
  | Enum e -> { decls with enums=(FieldMap.add id e decls.enums)}
  | Struct s -> { decls with structs=(FieldMap.add id s decls.structs)}

  let find_declaration decls ty = 
  let open Monad.MonadSyntax(MonadOption.M) in
  match ty with
  | Process id -> let+ p = FieldMap.find_opt id decls.processes in Process p
  | Method id ->  let+ m = FieldMap.find_opt id decls.methods in Method m
  | Struct id -> let+ s = FieldMap.find_opt id decls.structs in Struct s
  | Enum id -> let+ e = FieldMap.find_opt id decls.enums in Enum e

  let write_declarations _decls _filename = () (* todo *) 


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
 

module VariableDeclEnv = functor (D:DeclEnvType) (V:Variable) -> struct
  include D
  
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
  

  let get_function (_,g) name = D.find_declaration g name
    
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
      declare_var m n dummy_pos (V.to_var mut t) |> Result.get_ok (* there should not be any error*)
    ) env
    args
end
