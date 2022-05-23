open Llvm

module type Env = sig
  type t
  type value
  val empty : unit -> t
  val get_var : t -> string -> value
  val declare_var : t -> string -> value -> t
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

module SailEnv : (StackEnv with type value = llvalue) = 
struct
  module M = Map.Make(String)

  type value = llvalue
  type frame = value M.t
  type t = frame List.t

  let empty () = let c = M.empty in [c]

  let push_frame env s = 
    s :: env

  let pop_frame env = 
    List.tl env

  let new_frame env =
    let c = M.empty in
    push_frame env c

  let current_frame = function [] -> failwith "environnement is empty !" | h::t ->  h,t

  
  let print_env env =
    let rec aux env : string = 
      let c,env = current_frame env in
      let p =
        M.fold 
          (fun _ v -> let s = Printf.sprintf "%s " (value_name v) in fun n  ->  s ^ n) c "]"
      in let c = "\t[ " ^ p  in
      match env with
      | [] -> c ^ "\n"
      | _ -> c ^ "\n"  ^ aux env
    in try
    Logs.debug (fun m -> m "env : \n{\n %s }" (aux env) )
    with _ -> ()
  let get_var env name = 
    let rec aux env = 
      let current,env = current_frame env in
      match M.find_opt name current with 
      | Some v -> v
      | None  when env = [] ->  Printf.sprintf "variable %s doesn't exists !" name |> failwith
      | _ -> aux env
      in aux env

  let declare_var env name value =
    let current,env = current_frame env in
    match M.find_opt name current with 
    | Some _ -> Printf.sprintf "variable %s already exists !" name |> failwith
    | None -> 
      let upd_frame = M.add name value current in
      push_frame env upd_frame

end
