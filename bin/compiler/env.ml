open Llvm
open CompilerCommon
open Common.TypesCommon


module type Globals = sig
  type function_value = {ret:sailtype option; proto:llvalue}
  type t =  function_value FieldMap.t
  val get_declarations : sailor_functions -> llcontext -> llmodule -> t
  val find_declaration : t -> string -> function_value option

  val write_declarations : t -> string -> unit
end

  
module Globals : Globals = struct
  type function_value = {ret:sailtype option; proto:llvalue}
  type t = function_value FieldMap.t
    
  let declare_method (llc:llcontext) (llm:llmodule) (name:string) (m:sailor_method) (globals:t) : t = 
    let llvm_rt = match m.decl.ret with
    | Some t -> getLLVMType t llc llm
    | None -> void_type llc
    in
    let args_type = List.map (fun (_,arg) -> getLLVMType arg llc llm) m.decl.args |> Array.of_list in
    let method_t = function_type llvm_rt args_type in
    let name' = if String.equal "_Main_" name then "main" else name in
    let proto = declare_function name' method_t llm
    in FieldMap.add name {ret=m.decl.ret;proto} globals

  
  let get_declarations (funs:sailor_functions) llc llm : t = 
    Logs.debug (fun m -> m "generating llvm declarations");
    FieldMap.fold (declare_method llc llm) funs FieldMap.empty
    (* todo : enums & structs *)


  let find_declaration g name = 
    (* Logs.debug (fun m -> m "looking for declaration %s" name); *)
    FieldMap.find_opt name g 


  let write_declarations (g:t) name = 
    (* todo : define a format to easily retrieve information *)
    let filename = name ^ ".sli" in
    let def_file = open_out filename in
    FieldMap.iter (fun _ {ret;_} -> output_string def_file (string_of_sailtype ret)) g;
    close_out def_file 
end


module type Env = sig
  type t
  type sailor_value  
  val empty : Globals.t -> t

  val get_function : t -> string ->  Globals.function_value option
  val get_var : t -> string -> sailtype * sailor_value
  val declare_var : t -> string -> sailtype * sailor_value -> t
  val print_env : t -> unit

end

module type StackEnv = 
sig
  include Env
  type frame
  val push_frame :  t -> frame -> t
  val pop_frame : t -> t

  val new_frame : t -> t
  val current_frame : t -> frame * t
end

module SailEnv : (StackEnv with type sailor_value = llvalue) = 
struct
  type sailor_value = llvalue
  type frame = (sailtype * sailor_value) FieldMap.t
  type t = frame List.t * Globals.t

  let empty g = 
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
          (fun _ (_,v) -> let s = Printf.sprintf "%s " (value_name v) in fun n  ->  s ^ n) c "]"
      in let c = "\t[ " ^ p  in
      match env with
      | [],_ -> c ^ "\n"
      | _ -> c ^ "\n"  ^ aux env
    in 
    try
    Logs.debug (fun m -> m "env : \n{\n %s }" (aux e) )
    with _ -> failwith "problem with printing env (env empty?)"
  

  let get_function (_,g) name = Globals.find_declaration g name
    
  let get_var e name : sailtype * llvalue = 
    let rec aux env = 
      let current,env = current_frame env in
      match FieldMap.find_opt name current with 
      | Some v -> v
      | None  when fst env = [] ->  Printf.sprintf "variable %s doesn't exist !" name |> failwith
      | _ -> aux env
      in aux e

  let declare_var e name (tyval:sailtype * llvalue) =
    let current,_env = current_frame e in
    match FieldMap.find_opt name current with 
    | Some _ -> Printf.sprintf "variable %s already exists !" name |> failwith
    | None -> 
      let upd_frame = FieldMap.add name tyval current in
      push_frame _env upd_frame

end