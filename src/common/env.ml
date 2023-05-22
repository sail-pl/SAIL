open TypesCommon
module E = Error.Logger
open Monad
open MonadSyntax(E)


module type Declarations = sig
  type process_decl
  type method_decl
  type struct_decl
  type enum_decl
  type type_decl
end


 module type DeclEnvType = functor (D : Declarations) -> sig
  open D

  type t 

  type _ decl_ty = 
    | Method : method_decl decl_ty
    | Process : process_decl decl_ty
    | Struct : struct_decl decl_ty
    | Enum : enum_decl decl_ty
    | Type : type_decl decl_ty

  type ('a,_) search_type = 
  | All : 'a decl_ty -> ('a,(import * 'a) list) search_type
  | Self : ('a decl_ty) -> ('a,'a option) search_type
  | Specific : (string * 'a decl_ty) -> ('a,'a option) search_type

  val empty : t

  val add_decl : t -> string -> 'a -> 'a decl_ty -> t

  val find_decl : t -> string -> ('a,'b) search_type -> 'b

  val add_import_decls : t -> (import * t) -> t

  val get_imports : t -> import list

  val find_closest: string -> t -> string list
  val write_declarations : 'a -> 'b -> unit
  val print_declarations : t -> unit
  val iter_methods : (string -> method_decl -> unit) -> t -> unit
end 


module DeclarationsEnv : DeclEnvType = functor (D:Declarations) -> struct
  open D


  type _ decl_ty = 
    | Method : method_decl decl_ty
    | Process : process_decl decl_ty
    | Struct : struct_decl decl_ty
    | Enum : enum_decl decl_ty
    | Type : type_decl decl_ty

    type ('a,_) search_type = 
    | All : 'a decl_ty -> ('a,(import * 'a) list) search_type
    | Self : ('a decl_ty) -> ('a,'a option) search_type
    | Specific : (string * 'a decl_ty) -> ('a,'a option) search_type

  type env = {
    methods : method_decl FieldMap.t;
    processes : process_decl FieldMap.t;
    structs : struct_decl FieldMap.t;
    enums : enum_decl FieldMap.t;
    types : type_decl FieldMap.t;
  } 

  type t = {
    self : env;
    imports : (import * env) list
  }

  let empty = {
    self={
      methods = FieldMap.empty;
      processes = FieldMap.empty;
      structs = FieldMap.empty;
      enums = FieldMap.empty;
      types = FieldMap.empty
    } ; 
    imports = []
  }

  let get_imports (env:t) = List.map fst env.imports

  let get_field (type d) env: d decl_ty -> d FieldMap.t = function
  | Method -> env.methods
  | Process -> env.processes
  | Struct -> env.structs
  | Enum -> env.enums
  | Type -> env.types

  let add_decl(type d) (env:t) id (decl:d) : d decl_ty -> t = function
  | Process -> {env with self={env.self with processes=FieldMap.add id decl env.self.processes}}
  | Method -> {env with self={env.self with methods=FieldMap.add id decl env.self.methods}}
  | Struct -> {env with self={env.self with structs=FieldMap.add id decl env.self.structs}}
  | Type -> {env with self={env.self with types=FieldMap.add id decl env.self.types}}
  | Enum -> {env with self={env.self with enums=FieldMap.add id decl env.self.enums}}

  let find_decl_aux (type d) (env:env) id (ty : d decl_ty) :d option = 
    FieldMap.find_opt id (get_field env ty)


  let find_decl (type d) (type o) (env:t) id (s:(d,o) search_type) : o = 
    let open MonadOption in
    let open MonadOperator(M) in
    match s with
    | All d -> List.fold_left 
        (fun acc (m,env) -> acc @ ((find_decl_aux env id d >>| fun res -> m,res) |> list_of_option)) 
        []
        (({mname="_self"; dir=""; loc=dummy_pos},env.self)::env.imports) 

    | Self d -> find_decl_aux env.self id d

    | Specific (m,d) -> 
      if m = "_self" then
        find_decl_aux env.self id d
      else
        List.find_opt (fun ({mname;_},_) -> mname = m) env.imports
         >>= fun (_,env) -> find_decl_aux env id d 


  let add_import_decls (_to : t) (mname,from : import * t) = 
    let imports = (mname,from.self)::_to.imports in
    {_to with imports}


  let write_declarations _decls _filename = () (* todo *) 

  let iter_methods f env = FieldMap.iter f env.self.methods


  let print_declarations env = 
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "process %s\n" n) env.self.processes;
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "method %s\n" n)  env.self.methods;
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "struct %s\n" n)  env.self.structs;
    FieldMap.iter (fun n _ -> Printf.fprintf stdout "enum %s\n" n)  env.self.enums;
    Printf.fprintf stdout "There are %i imports : %s \n" (List.length env.imports) (String.concat " " (List.map (fun ({mname;_},_) -> mname) env.imports))


  let find_closest name env : string list =
    if String.length name > 3 then
      let check = (fun n  _  l -> if Error.levenshtein_distance n name < 3 then n::l else l) in
      FieldMap.fold check env.self.methods []
      |> fun l -> FieldMap.fold check env.self.processes l
      |> fun l -> FieldMap.fold check env.self.structs l
      |> fun l -> FieldMap.fold check env.self.enums l
    else []
end 


module type Variable = sig
  type t
  val string_of_var : t -> string

  val to_var : string -> bool -> sailtype -> t 
end
 
module VariableEnv (V : Variable) = struct
  type variable = loc * V.t
  type frame = variable FieldMap.t
  type t = frame list
  let empty : t = [FieldMap.empty]
  let push_frame env s = s :: env

  let pop_frame env = List.tl env

  let new_frame e =
    let c = FieldMap.empty in
    push_frame e c

  let current_frame = function [] -> failwith "environnement is empty !" | (h::t) ->  h,t

  let print_env (e:t) =
    let rec aux (env:t) : string = 
      let c,env = current_frame env in
      let p =
        FieldMap.fold 
          (fun n (_,v) -> let s = Printf.sprintf "(%s:%s) " n (V.string_of_var v) in fun n  ->  s ^ n) c "]"
      in let c = "\t[ " ^ p  in
      match env with
      | [] -> c ^ "\n"
      | _ -> c ^ "\n"  ^ aux env
    in 
    try
    Printf.sprintf "env : \n{\n %s }" (aux e)
    with _ -> failwith "problem with printing env (env empty?)"

    let get_var e name  = 
    let rec aux env = 
      let current,env = current_frame env in
      match FieldMap.find_opt name current with 
      | Some v -> Some v
      | None  when env = [] -> None
      | _ -> aux env
      in aux e

  let declare_var (e:t) name (l,_ as v:variable) : frame list E.t =
    let current,env = current_frame e in
    match FieldMap.find_opt name current with 
    | None -> 
      let upd_frame = FieldMap.add name v current in
      push_frame env upd_frame |> E.pure
    | Some _ -> let+ () = E.throw @@ Error.make l @@ Printf.sprintf "variable %s already declared !" name in e


    let init_env (args:param list) : t E.t =
      let open Monad.MonadFunctions(Error.Logger) in
      let env = empty |> new_frame in
      foldRightM (fun p m ->
        let v = V.to_var p.id p.mut p.ty  in 
        declare_var m p.id (p.loc,v)
      ) args
      env

    let update_var (e:t) l (f:variable -> variable E.t ) name : t E.t =
      let rec aux env  = 
        let current,env = current_frame env in
        match FieldMap.find_opt name current with 
        | Some v -> let+ v' = f v in FieldMap.add name v' current :: env
        | None  when env = [] -> let+ () = E.throw @@ Error.make l @@ Printf.sprintf "variable %s not found" name in e
        | _ -> let+ e = aux env in current :: e
        in aux e 
  

end

module VariableDeclEnv = functor (D:Declarations) (V:Variable) -> struct
  module D = DeclarationsEnv(D)
  module VE = VariableEnv(V)

  type t = VE.t * D.t

  let get_decl (_,g) name = D.find_decl g name

  let get_imports (_,g) = D.get_imports g

  let get_closest (_,g) name = D.find_closest name g
  let get_var (env,_) id = VE.get_var env id
  let declare_var (env,g) id v = let+ env = VE.declare_var env id v in env,g

  let update_var (env,g) l v id= let+ env = VE.update_var env l v id in env,g
  let new_frame (env,g) = VE.new_frame env,g
  let pop_frame (env,g) = VE.pop_frame env,g
  let get_env (env,_) = env

  let empty g : t = VE.empty,g


  let get_start_env (decls:D.t) (args:param list) : t E.t =
    let+ venv = VE.init_env args in
    venv,decls
end
