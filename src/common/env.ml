
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

  val empty : unit -> t
  val add_declaration : t -> string -> decl -> t
  val find_declaration : t -> decl_ty -> decl option
  val write_declarations : t -> string -> unit
end


module DeclarationsEnv (D:Declarations) = struct
  module M = Map.Make(String)

  type t = {
    methods : D.method_decl M.t;
    processes : D.process_decl M.t;
    structs : D.struct_decl M.t;
    enums : D.enum_decl M.t;
  } 

  type ('a, 'b, 'c, 'd) ty = Process of 'a | Method of 'b | Struct of 'c | Enum of 'd
  type decl = (D.process_decl, D.method_decl, D.struct_decl, D.enum_decl) ty
  type decl_ty = (string,string,string,string) ty


  let empty () = {
    methods = M.empty;
    processes = M.empty;
    structs = M.empty;
    enums = M.empty;
  }

  let add_declaration decls id (d:decl) = match d with
  (* todo : check name conflict *)
  | Process p -> { decls with processes=(M.add id p decls.processes)}
  | Method m -> { decls with methods=(M.add id m decls.methods)}
  | Enum e -> { decls with enums=(M.add id e decls.enums)}
  | Struct s -> { decls with structs=(M.add id s decls.structs)}

  let find_declaration decls ty = 
  let open Monad.MonadSyntax(MonadOption.M) in
  match ty with
  | Process id -> let+ p = M.find_opt id decls.processes in Process p
  | Method id ->  let+ m = M.find_opt id decls.methods in Method m
  | Struct id -> let+ s = M.find_opt id decls.structs in Struct s
  | Enum id -> let+ e = M.find_opt id decls.enums in Enum e

  let write_declarations _decls _filename = () (* todo *) 


  let print_declarations decls = 
    M.iter (fun n _ -> Printf.fprintf stdout "process %s\n" n) decls.processes;
    M.iter (fun n _ -> Printf.fprintf stdout "method %s\n" n) decls.methods;
    M.iter (fun n _ -> Printf.fprintf stdout "struct %s\n" n) decls.structs;
    M.iter (fun n _ -> Printf.fprintf stdout "enum %s\n" n) decls.enums

end

(* module type S = 
sig
  type globals
  type t
  type variable
  val empty : globals -> t

  val get_var : t -> string -> variable
  val declare_var : t -> string -> variable -> t
  val print_env : t -> string
  
  type frame
  val push_frame :  t -> frame -> t
  val pop_frame : t -> t

  val new_frame : t -> t
  val current_frame : t -> frame * t
end *)

module type Variable = sig
  type t
  val string_of_var : t -> string
end


module VariableEnv (V:Variable) (D:DeclEnvType) = struct
  
  module M = Map.Make(String)

  type variable = V.t
  type frame = variable M.t
  type t = frame list * D.t

  let empty g : t = 
    let c = M.empty in [c],g

  let push_frame (env,g) s = 
    s :: env, g

  let pop_frame (env,g) = 
    List.tl env, g

  let new_frame e =
    let c = M.empty in
    push_frame e c

  let current_frame = function [],_ -> failwith "environnement is empty !" | (h::t),g ->  h,(t,g)

  
  let print_env (e:t) =
    let rec aux (env:t) : string = 
      let c,env = current_frame env in
      let p =
        M.fold 
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
    
  let get_var e name loc = 
    let rec aux env = 
      let current,env = current_frame env in
      match M.find_opt name current with 
      | Some v -> Result.ok v
      | None  when fst env = [] ->  Result.error [loc,Printf.sprintf "variable %s doesn't exist !" name]
      | _ -> aux env
      in aux e

  let declare_var e name tyval loc =
    let current,_env = current_frame e in
    match M.find_opt name current with 
    | Some _ -> Result.error [loc,Printf.sprintf "variable %s already exists !" name]
    | None -> 
      let upd_frame = M.add name tyval current in
      push_frame _env upd_frame |> Result.ok
end