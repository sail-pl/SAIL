open TypesCommon
module E = Error.Logger
open Monad
open MonadSyntax(E)
open MonadOperator(E)

module type Declarations = sig
  type process_decl
  type method_decl
  type struct_decl
  type enum_decl
  type type_decl
  (* val string_of_process : process_decl -> string
  val string_of_method : method_decl -> string
  val string_of_enum : enum_decl -> string
  val string_of_struct : struct_decl -> string
  val string_of_type : type_decl -> string *)
end


module type DeclEnvType = functor (D : Declarations) -> sig
  open D

  type t 

  type 'a container

  type decls = (method_decl, process_decl,struct_decl,enum_decl,type_decl) decl_sum

  type _ decl_ty = 
    | Method : method_decl decl_ty
    | Process : process_decl decl_ty
    | Struct : struct_decl decl_ty
    | Enum : enum_decl decl_ty
    | Type : type_decl decl_ty
    | Filter : unit_decl list -> decls decl_ty

  type ('a,_) search_type = 
  | All : 'a decl_ty -> ('a,(import * 'a) list) search_type
  | Self : ('a decl_ty) -> ('a,'a option) search_type
  | Specific : (string * 'a decl_ty) -> ('a,'a option) search_type

  type _ update_type = 
  | Self :  'a decl_ty -> 'a update_type
  | Specific : string * 'a decl_ty -> 'a update_type

  type env

  val empty : t

  val get_name : t -> string

  val set_name : string -> t -> t
  val add_decl : string -> 'd -> 'd decl_ty -> t -> t E.t

  val remove_decl : string -> 'd decl_ty  -> t -> t E.t

  val update_decl : string -> 'd -> 'd update_type -> t -> t
  val find_decl : string -> ('a,'b) search_type -> t -> 'b
  val add_import_decls : (import * t) -> t -> t
  val get_imports : t -> import list
  val replace_imports_with : t -> t -> t
  val remove_imports : t -> t
  val find_closest: string -> t -> string list
  val write_declarations : 'a -> 'b -> unit
  val string_of_env : t -> string
  val iter_decls : (string -> 'd -> unit) -> ('d,'o) search_type -> t -> unit E.t
  val map_decls : ('a -> 'b) -> 'a container -> 'b container
  val fold_decls : (string -> 'd -> 'a -> 'a) -> 'a -> 'd decl_ty -> t -> 'a
  val get_own_decls : t -> env
  val get_decls :'d decl_ty ->  env -> 'd container
  val overwrite_decls : 'd container -> 'd decl_ty -> env -> env
  val container_length : 'd container -> int
  val to_seq : 'a container -> (string * 'a) Seq.t
  val of_seq : (string * 'a) Seq.t -> 'a container

  module MethodSeq : (Sequencable with type t = D.method_decl container and type seq_ty = string * D.method_decl)
  module StructSeq : (Sequencable with type t = D.struct_decl container and type seq_ty = string * D.struct_decl)
  module EnumSeq : (Sequencable with type t = D.enum_decl container and type seq_ty = string * D.enum_decl) 
  module ProcessSeq : (Sequencable with type t = D.process_decl container and type seq_ty = string * D.process_decl)
  module TypeSeq : (Sequencable with type t = D.type_decl container and type seq_ty = string * D.type_decl)

end 


module DeclarationsEnv : DeclEnvType  = functor (D:Declarations) -> struct
  open D
  open MonadOperator(E)

  type decls = (method_decl, process_decl,struct_decl,enum_decl,type_decl) decl_sum

  type 'a container = 'a FieldMap.t

  type _ decl_ty = 
    | Method : method_decl decl_ty
    | Process : process_decl decl_ty
    | Struct : struct_decl decl_ty
    | Enum : enum_decl decl_ty
    | Type : type_decl decl_ty
    | Filter : unit_decl list -> decls decl_ty

  type ('a,_) search_type = 
    | All : 'a decl_ty -> ('a,(import * 'a) list) search_type
    | Self : ('a decl_ty) -> ('a,'a option) search_type
    | Specific : (string * 'a decl_ty) -> ('a,'a option) search_type

  type _ update_type = 
    | Self :  'a decl_ty -> 'a update_type
    | Specific : string * 'a decl_ty -> 'a update_type

  type env = {
    methods : method_decl container;
    processes : process_decl container;
    structs : struct_decl container;
    enums : enum_decl container;
    types : type_decl container;
  } 

  type t = {
    self : env;
    imports : (import * env) list;
    name : string;
  }

  let empty = {
    self={
      methods = FieldMap.empty;
      processes = FieldMap.empty;
      structs = FieldMap.empty;
      enums = FieldMap.empty;
      types = FieldMap.empty;
    } ; 

    imports = [];

    name = String.empty
  }

  let get_name = fun t -> t.name

  let set_name (name:string) t : t = {t with name}

  let get_imports (env:t) = List.map fst env.imports
  let get_own_decls env = env.self

  let get_decls (type d) : d decl_ty -> env -> d FieldMap.t = function
  | Method -> fun env -> env.methods
  | Process -> fun env -> env.processes
  | Struct -> fun env -> env.structs
  | Enum -> fun env -> env.enums
  | Type -> fun env -> env.types
  | Filter decls -> fun env -> Seq.(
    let get d f e = if (List.mem d decls) then map f e else empty in
    Seq.empty
    |> append (get (M ()) (fun (id,d) -> id,M d) (FieldMap.to_seq env.methods))
    |> append (get (P ()) (fun (id,d) -> id,P d) (FieldMap.to_seq env.processes)) 
    |> append (get (S ()) (fun (id,d) -> id,S d) (FieldMap.to_seq env.structs))
    |> append (get (E ()) (fun (id,d) -> id,E d) (FieldMap.to_seq env.enums))
    |> append (get (T ()) (fun (id,d) -> id,T d) (FieldMap.to_seq env.types))
    |> FieldMap.of_seq)


  let update_decls (type d) (f: d FieldMap.t -> d FieldMap.t) (ty: d decl_ty) (env:env) : env =
    let res = f (get_decls ty env) in
    match ty with
    | Process -> {env with processes=res}
    | Method -> {env with methods= res}
    | Struct -> {env with structs= res}
    | Type -> {env with types= res}
    | Enum -> {env with enums=res}
    | Filter _ -> failwith "Filter shouldn't be used in update_decls"

  let update_decl (type d) (id: string) (decl : d) (ty : d update_type) (env:t) : t = match ty with
    | Self ty ->  {env with self=update_decls (FieldMap.update id (function Some _d -> Some decl | None -> None)) ty env.self}
    | Specific (name,ty) -> 
      let imports = List.map (fun (i,e) -> if i.mname = name then i,update_decls (FieldMap.add id decl) ty e else (i,e)) env.imports in
      {env with imports}
  let overwrite_decls (type d) (field: d container) = update_decls (fun _ -> field) 

  let add_decl (type d) id (decl:d) (ty: d decl_ty) (env:t) : t E.t = 
    E.throw_if (Error.make dummy_pos @@ Fmt.str "duplicate declarations for '%s'" id) (FieldMap.mem id (get_decls  ty env.self))
    >>= fun () -> return {env with self=update_decls (FieldMap.add id decl) ty env.self}

  let remove_decl id (ty:'a decl_ty) t = 
    let new_env = update_decls (FieldMap.remove id) ty t.self in
    let+ () = E.throw_if 
      (Error.make dummy_pos @@ Fmt.str "attempting to remove unknown declaration '%s'" id) 
      (new_env <> t.self)
    in {t with self=new_env}

  let to_seq = FieldMap.to_seq
  let of_seq = FieldMap.of_seq

  let container_length = FieldMap.cardinal

  let string_of_declarations env : string = 
    FieldMap.fold (fun n _ s -> Fmt.str  "process %s\n %s" n s) env.processes ""
    |> FieldMap.fold (fun n _ s -> Fmt.str "method %s\n %s" n s)  env.methods 
    |> FieldMap.fold (fun n _ s -> Fmt.str  "struct %s\n %s" n s)  env.structs
    |> FieldMap.fold (fun n _ s -> Fmt.str  "enum %s\n %s" n s)  env.enums
    |> FieldMap.fold (fun n _ s -> Fmt.str  "type %s\n %s" n s)  env.types

  let string_of_env env = 
    Fmt.str "Declarations : \n %s \n There are %i imports : \n %s \n" 
    (string_of_declarations env.self) 
    (List.length env.imports) 
    (String.concat "\n" (List.map (fun ({mname;_},e) -> Fmt.str "%s : \n\n %s"  mname (string_of_declarations e)) env.imports))


  let find_decl (type d) (type o) id (s:(d,o) search_type) (env:t) : o = 
    let find_decl_aux (type d) id (ty : d decl_ty) (env:env) : d option = 
      FieldMap.find_opt id (get_decls ty env)
    in

    let open MonadOption in
    let open MonadOperator(M) in
    match s with
    | All d -> List.fold_left 
        (fun acc (m,env) -> acc @ ((find_decl_aux id d env >>| fun res -> m,res) |> list_of_option)) 
        []
        (({mname=env.name; dir=""; loc=dummy_pos; proc_order=0},env.self)::env.imports) 

    | Self d -> find_decl_aux id d env.self

    | Specific (m,d) -> 
      if m = env.name then
        find_decl_aux id d env.self
      else
        match List.find_opt (fun ({mname;_},_) -> mname = m) env.imports with
        | None -> Logs.debug (fun c -> c "looking for '%s' : module %s not in env imports" id m); None 
        | Some (_,env) -> find_decl_aux id d env

  let add_import_decls (i,from : import * t) (_to : t)  = 
    let imports = (i,from.self)::_to.imports in
    {_to with imports}

  let replace_imports_with (_with : t) (from : t) : t = {from with imports=_with.imports}

  let remove_imports (e : t ) = {e with imports = []}
  let write_declarations _decls _filename = () (* todo *) 

  let iter_decls (type d) (type o) f (s:(d,o) search_type) (env:t) : unit E.t = match s with
  | All ty -> FieldMap.iter f (get_decls ty env.self); List.iter (fun (_,env) -> FieldMap.iter f (get_decls ty env)) env.imports |> return
  | Specific (m,d) -> 
    if m = env.name  then
      return (FieldMap.iter f (get_decls d env.self))
    else
    let+ env = E.throw_if_none (Error.make dummy_pos "can't happen")
                              (List.find_opt (fun ({mname;_},_) -> mname = m) env.imports)
                                in
          FieldMap.iter f (get_decls d (snd env) )

  | Self d -> return (FieldMap.iter f (get_decls d env.self ))

  let map_decls f = FieldMap.map f

  let fold_decls : (string -> 'd -> 'a -> 'a) -> 'a -> 'd decl_ty -> t -> 'a = fun f accu ty env -> 
    FieldMap.fold f (get_decls ty env.self) accu

  let find_closest name env : string list =
    if String.length name > 3 then
      let check = (fun n  _  l -> if Error.levenshtein_distance n name < 3 then n::l else l) in
      FieldMap.fold check env.self.methods []
      |> fun l -> FieldMap.fold check env.self.processes l
      |> fun l -> FieldMap.fold check env.self.structs l
      |> fun l -> FieldMap.fold check env.self.enums l
    else []

  module MakeSequencable(T : Type) : Sequencable with type t = T.t container and type seq_ty = string * T.t = 
  struct
          type t = T.t container
          type seq_ty = string * T.t
          let to_seq : T.t container -> seq_ty Seq.t = to_seq
          let of_seq : seq_ty Seq.t -> T.t container = of_seq
  end

      
  module MethodSeq = MakeSequencable(struct type t = D.method_decl end)
  module TypeSeq = MakeSequencable(struct type t = D.type_decl end)
  module EnumSeq = MakeSequencable(struct type t = D.enum_decl end)
  module StructSeq = MakeSequencable(struct type t = D.struct_decl end)
  module ProcessSeq = MakeSequencable(struct type t = D.process_decl end)
end 


module type Variable = sig
  type t
  val string_of_var : t -> string

  val param_to_var : param -> t 
end


module type VariableEnvType = functor (V : Variable) -> sig
  type variable = loc * V.t
  type frame = variable FieldMap.t
  type t = {stack:frame list}
  val empty : t
  val new_frame : t -> t
  val string_of_env : t -> string
  val get_var : string -> t -> variable option
  val declare_var : string -> variable -> t -> t E.t
  val update_var : loc -> (variable  -> variable E.t) -> string -> t -> t E.t
  val pop_frame : t -> t

  val init_env : param list -> t E.t
end



module VariableEnv : VariableEnvType = functor (V : Variable) -> struct
  type variable = loc * V.t
  type frame = variable FieldMap.t
  type t = {stack:frame list}
  let empty : t = let c = FieldMap.empty in {stack=[c]}
  
  let push_frame env s = s :: env

  let pop_frame env =  {stack=List.tl env.stack}

  let new_frame (e:t) =
    let c = FieldMap.empty in
    {stack=push_frame e.stack c}

  let current_frame : frame list -> frame * frame list = function [] -> failwith "environnement is empty !" | (h::t) ->  h,t

  let string_of_env (e:t) =
    let rec aux (env:frame list) : string = 
      let c,stack = current_frame env in
      let p =
        FieldMap.fold 
          (fun n (_,v) -> let s = Printf.sprintf "(%s:%s) " n (V.string_of_var v) in fun n  ->  s ^ n) c "]"
      in let c = "\t[ " ^ p  in
      match stack with
      | [] -> c ^ "\n"
      | _ -> c ^ "\n"  ^ aux stack
    in 
    try
    Printf.sprintf "env : \n{\n %s }" (aux e.stack)
    with _ -> failwith "problem with printing env (env empty?)"

    let get_var name e   = 
    let rec aux env = 
      let current,env = current_frame env in
      match FieldMap.find_opt name current with 
      | Some v -> Some v
      | None  when env = [] -> None
      | _ -> aux env
      in aux e.stack

  let declare_var name (l,_ as v:variable) (e:t): t E.t =
    let current,stack = current_frame e.stack in
    match FieldMap.find_opt name current with 
    | None -> 
      let upd_frame = FieldMap.add name v current in
      let stack = push_frame stack upd_frame in {stack} |> E.pure
    | Some _ -> 
      E.throw (Error.make l @@ Printf.sprintf "variable %s already declared in current frame!" name) 
      >>| fun () -> e


    let init_env (args:param list) : t E.t =
      let open Monad.MonadFunctions(Error.Logger) in
      let env = empty |> new_frame in
        ListM.fold_right (fun (p:param) ->
        let v = V.param_to_var p  in 
        declare_var p.id (p.loc,v)
      ) args
      env

    let update_var l (f:variable -> variable E.t ) name (e:t) : t E.t =
      let rec aux (stack: frame list)  = 
        let current,stack = current_frame stack in
        match FieldMap.find_opt name current with 
        | Some v -> let+ v' = f v in FieldMap.add name v' current :: stack
        | None  when stack = [] -> E.throw (Error.make l @@ Printf.sprintf "variable %s not found" name) 
          >>| fun () -> e.stack
        | _ -> let+ e = aux stack in current :: e
      in 
      let+ stack = aux (e.stack) in 
      {stack}
  

end

module VariableDeclEnv = functor (D:Declarations) (V:Variable) -> struct
  module D = DeclarationsEnv(D)
  module VE = VariableEnv(V)

  type t = VE.t * D.t

  let get_decl name ty (_,g) = D.find_decl name ty g 

  let add_decl name d ty (v,g) = let+ g = D.add_decl name d ty g in v,g

  let get_imports (_,g) = D.get_imports g

  let get_closest name (_,g)  = D.find_closest name g
  let get_var id (env,_) = VE.get_var id env
  let declare_var id v (env,g) = let+ env = VE.declare_var id v env  in env,g

  let update_var l v id (env,g) = let+ env = VE.update_var l v id env in env,g
  let new_frame (env,g) = VE.new_frame env,g
  let pop_frame (env,g) = VE.pop_frame env,g
  let get_env (env,_) = env

  let empty g : t = VE.empty,g

  let get_start_env (decls:D.t) (args:param list) : t E.t =
    let+ venv = VE.init_env args in
    venv,decls
end
