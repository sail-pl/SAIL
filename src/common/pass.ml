open TypesCommon


type function_proto = 
{
  ret : sailtype option;
  args : (string * sailtype) list;
  generics : string list;
}

type enum_proto = 
{
  generics : string list;
  injections : (string * sailtype list) list;
}

type struct_proto = 
{
  generics : string list;
  fields : (string * sailtype) list
}


type declarations = {
  methods : function_proto FieldMap.t;
  processes : function_proto FieldMap.t;
  structs : struct_proto FieldMap.t;
  enums : enum_proto FieldMap.t;
}


type type_env = sailtype FieldMap.t List.t (* List is used for scoping *)

(* todo : use sail_env *)
let current_frame = function [] -> failwith "environnement is empty !" | (h::t) ->  h,t

let push_frame ts s = s :: ts

let pop_frame = function _::t  -> t | [] -> failwith "popping empty frame"

let new_frame ts =
  let c = FieldMap.empty in
  push_frame ts c

let get_var e name = 
  let rec aux env = 
    let current,next = current_frame env in
    match FieldMap.find_opt name current with 
    | Some v -> v
    | None when next = [] ->  Printf.sprintf "variable %s doesn't exist !" name |> failwith
    | _ -> aux next
    in aux e

let declare_var ts name value =
  let current,next = current_frame ts in
  match FieldMap.find_opt name current with 
  | Some _ -> Printf.sprintf "variable %s already exists !" name |> failwith
  | None -> 
    let upd_frame = FieldMap.add name value current in
    push_frame next upd_frame




module type Body = sig
  type in_body
  type out_body
  val translate : in_body ->  type_env -> declarations  -> out_body
end



module type S = sig
  type in_body
  type out_body
  val translate_module : in_body sailModule -> out_body sailModule
end


module Make (T: Body) : S with type in_body = T.in_body and type out_body = T.out_body = 
struct
  type in_body = T.in_body
  type out_body = T.out_body


  let collect_declarations (m :T.in_body sailModule) : declarations =
    let methods = List.fold_left (
      fun acc m -> 
        let ret = m.m_rtype 
        and args = m.m_params 
        and generics = m.m_generics in 
        FieldMap.add m.m_name {ret;args;generics} acc
    ) FieldMap.empty m.methods 
    (* todo: collect externals  *)

    and processes = List.fold_left (
      fun acc p -> 
        let ret = None
        and args = fst p.p_interface
        and generics = p.p_generics in 
        FieldMap.add p.p_name {ret;args;generics} acc
    ) FieldMap.empty m.processes

    and structs = List.fold_left (
      fun acc s ->  
        FieldMap.add s.s_name {generics=s.s_generics;fields=s.s_fields} acc
    ) FieldMap.empty m.structs 

    and enums = List.fold_left (
      fun acc e ->  
        FieldMap.add e.e_name {generics=e.e_generics;injections=e.e_injections} acc
    ) FieldMap.empty m.enums 
  in {methods;processes;structs;enums}

  let get_start_env args =
    let env = new_frame [] in
    List.fold_left (fun m (n,t) -> declare_var m n t) env args

  let translate_method (m:T.in_body method_defn) (decls : declarations) : T.out_body method_defn = 
    let start_env = get_start_env m.m_params in
    { m with m_body = T.translate m.m_body start_env decls}

  let translate_process (p : T.in_body process_defn) (decls : declarations) : T.out_body process_defn = 
    let start_env = get_start_env (p.p_interface |> fst) in
    { p with p_body = T.translate p.p_body start_env decls}

  let translate_module (m: T.in_body sailModule) : T.out_body sailModule = 
    let decls = collect_declarations m in
    {
      m with 
      methods = List.map (fun m -> translate_method m decls) m.methods ; 
      processes = List.map (fun p -> translate_process p decls) m.processes 
    }
    
end