open Llvm
open Common
open Globals


module type Env = sig
  type t
  type sailor_value  
  val empty : Globals.t -> t

  val get_method : t -> string ->  function_value option
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
  

  let get_method (_,g) name =
    Globals.find_declaration g name
    
  let get_var e name : sailtype * llvalue = 
    let rec aux env = 
      let current,env = current_frame env in
      match FieldMap.find_opt name current with 
      | Some v -> v
      | None  when fst env = [] ->  Printf.sprintf "variable %s doesn't exists !" name |> failwith
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