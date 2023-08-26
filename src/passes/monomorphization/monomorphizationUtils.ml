open Common
open TypesCommon 
open Monad
open IrHir
module E = Logging.Logger
module Env = SailModule.SailEnv(IrMir.AstMir.V)
open UseMonad(E)

type in_body = IrMir.AstMir.mir_function
type out_body = {
  monomorphics : in_body method_defn list; 
  polymorphics : in_body method_defn list; 
  processes : (HirUtils.statement,HirUtils.expression) SailParser.AstParser.process_body process_defn list
}


type sailor_args = sailtype dict
type varTypesMap = Env.t
type monomorphics = sailor_args dict
type sailor_function = in_body method_defn
type 'a sailor_method = { methd : 'a method_defn; generics : sailor_args }
type sailor_functions = in_body sailor_method FieldMap.t

let print_method_proto (name : string) (methd : in_body sailor_method) =
  let args_type =
    List.map (fun (p : param) -> p.ty) methd.methd.m_proto.params
  in
  let args =
    String.concat ","
      (List.map (fun t -> string_of_sailtype (Some t)) args_type)
  in
  let methd_string = Printf.sprintf "method %s (%s)" name args in
  Logs.debug (fun m -> m "%s" methd_string)



let resolveType (arg : sailtype) (m_param : sailtype) (generics : string list) (resolved_generics : sailor_args) : (sailtype * sailor_args) E.t =
  let rec aux ((aloc, a) : sailtype) ((mloc, m) : sailtype) (g : sailor_args) : (sailtype * sailor_args) E.t =
    match a,m with
    | Bool, Bool -> return ((aloc,Bool), g)
    | Int x, Int y when x = y -> return ((aloc,Int x), g)
    | Float, Float -> return ((aloc,Float), g)
    | Char, Char -> return ((aloc,Char), g)
    | String, String -> return ((aloc,String), g)
    | ArrayType (at, s), ArrayType (mt, _) -> let+ t,g = aux at mt g in (aloc,ArrayType (t, s)), g
    | GenericType _g1, GenericType _g2 -> return ((aloc,Int 32),g)
      (* E.throw Logging.(make_msg dummy_pos @@ Fmt.str "resolveType between generic %s and %s" g1 g2) *)
    
    | _, GenericType gt ->
        let* () = E.throw_if Logging.(make_msg mloc @@ Fmt.str "generic type %s not declared" gt) (not @@ List.mem gt generics) in
        begin
          match List.assoc_opt gt g with
          | None -> return ((aloc,a), (gt, (aloc,a)) :: g)
          | Some (lt,t) ->  
            E.throw_if 
              Logging.(make_msg lt @@ Fmt.str "generic type mismatch : %s -> %s vs %s" gt (string_of_sailtype (Some (lt,t))) (string_of_sailtype (Some (aloc,a)))) 
              (t <> a) 
            >>| fun () -> (aloc,a), g
        end
    | RefType (at, _), RefType (mt, _) -> aux at mt g

    | CompoundType _, CompoundType _ -> failwith "todocompoundtype"
    | Box _at, Box _mt -> failwith "todobox"
    | _ -> E.throw Logging.(make_msg dummy_pos @@ Fmt.str "cannot happen : %s vs %s" (string_of_sailtype (Some (aloc,a))) (string_of_sailtype (Some (mloc,m))))
  in
  aux arg m_param resolved_generics

let degenerifyType (t : sailtype) (generics : sailor_args) : sailtype E.t =
  let rec aux (l,t) = 
    let+ t = match t with
      | Bool -> return Bool
      | Int n -> return (Int n)
      | Float -> return Float
      | Char -> return Char
      | String -> return String
      | ArrayType (t, s) -> let+ t = aux t in ArrayType (t, s)
      | Box t -> let+ t = aux t in Box t
      | RefType (t, m) -> let+ t = aux t in RefType (t, m)
      | GenericType n -> 
        let+ t = E.throw_if_none Logging.(make_msg dummy_pos @@ Fmt.str "generic type %s not present in the generics list" n) (List.assoc_opt n generics) in
        snd t
      | CompoundType _ -> failwith "todo compoundtype"
      in l,t
  in
  aux t

let check_args (caller_args : sailtype list) (f:sailor_function)  : sailor_args E.t =
  let margs = List.map (fun (p:param) -> p.ty) f.m_proto.params in
  Logs.debug (fun m -> m "caller args : %s"
        (List.fold_left (fun acc t ->Printf.sprintf "%s %s," acc (string_of_sailtype (Some t))) "" caller_args));
  Logs.debug (fun m ->
      m "method args : %s"
        (List.fold_left (fun acc t -> Printf.sprintf "%s %s," acc (string_of_sailtype (Some t))) "" margs));

  let args = if f.m_proto.variadic then List.filteri (fun i _ -> i < (List.length margs)) caller_args else caller_args in

let+ resolved_generics = ListM.fold_right2 (fun ca a g -> resolveType ca a f.m_proto.generics g >>| snd) args margs [] in
  List.rev resolved_generics

let find_callable (name : string) (sm : _ SailModule.methods_processes SailModule.t) : sailor_function option E.t =
  (* fixme imports *)
  Logs.debug (fun m -> m "looking for function %s" name);
  Logs.debug (fun m -> m "name is %s" name);
  Logs.debug (fun m -> m "%s" @@ SailModule.DeclEnv.string_of_env sm.declEnv);
  match SailModule.DeclEnv.find_decl name (All (Method)) sm.declEnv with

  | [_,_] -> 
    return @@ List.find_opt (fun m -> m.m_proto.name = name) sm.body.methods
    
  | [] -> E.throw Logging.(make_msg dummy_pos @@ Fmt.str "mono : %s not found" name)
  | l -> E.throw Logging.(make_msg dummy_pos @@ Fmt.str "multiple symbols for %s : %s" name (List.map (fun (i,_) -> i.mname) l |> String.concat " "))