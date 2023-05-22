open Common
open TypesCommon
open IrHir
open ThirMonad
open Monad

open MonadSyntax(ES)
open MonadOperator(ES)
open MonadFunctions(ES)

type expression = (loc * sailtype, import) AstHir.expression
type statement = (loc,import,expression) AstHir.statement

let degenerifyType (t: sailtype) (generics: sailtype dict) loc : sailtype ES.t =
  let rec aux = function
  | Bool -> return Bool
  | Int -> return Int 
  | Float -> return Float
  | Char -> return Char
  | String -> return String
  | ArrayType (t,s) -> let+ t = aux t in ArrayType (t, s)
  | CompoundType (_,_name, _tl)-> ES.throw (Error.make loc "todo compoundtype")
  | Box t -> let+ t = aux t in Box t
  | RefType (t,m) -> let+ t = aux t in RefType (t,m)
  | GenericType t when generics = [] -> ES.throw @@ Error.make loc (Printf.sprintf "generic type %s present but empty generics list" t)
  | GenericType n -> 
    begin
      match List.assoc_opt n generics with
      | Some GenericType t -> return (GenericType t)
      | Some t -> aux t
      | None -> ES.throw @@ Error.make loc (Printf.sprintf "generic type %s not present in the generics list" n) 
    end
  in
  aux t


let matchArgParam (l,arg: loc * sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: sailtype dict) : (sailtype * sailtype dict) ES.t =
  let open MonadSyntax(ES) in
  let rec aux (a:sailtype) (m:sailtype) (g: sailtype dict) (alias_checked : string list) = 
  match (a,m) with
  | Bool,Bool -> return (Bool,g)
  | Int,Int -> return (Int,g)
  | Float,Float -> return (Float,g)
  | Char,Char -> return (Char,g)
  | String,String -> return (String,g)
  | ArrayType (at,s),ArrayType (mt,s') -> 
    if s = s' then
      let+ t,g = aux at mt g alias_checked in ArrayType (t,s),g
    else
      ES.throw @@ Error.make l (Printf.sprintf "array length mismatch : wants %i but %i provided" s' s)
  
      
  | CompoundType (mloc,(l,name),[]), t | t,CompoundType (mloc,(l,name),[]) ->     
    begin
      (* check if circular type aliasing *)
      let* () = ES.throw_if (List.mem name alias_checked) 
      (Error.make l @@ "circular type aliasing : " ^ String.concat " -> " (List.rev alias_checked) ^ " -> " ^ name)
      in
      let alias_checked = name::alias_checked in
      (* check if extern type *)
      match mloc with
      | Some s -> let* ty_t = ES.get_decl name (Specific (s,Type)) in 
                  let* ty_t = ES.throw_if_none ty_t (Error.make l "cannot happen") in 
                  let* ty = ES.throw_if_none ty_t.ty (Error.make l "todo abstract type") in
                  aux t ty g alias_checked

      | None -> (* if not, ... *)
        begin
        let* env = ES.get_decl name (Self Type) in 
        match env with
        | Some {ty=Some ty_t; _ } ->  (* type alias, get it and compare again *) 
          aux t ty_t g alias_checked
        | Some {ty=None; _ } -> (* abstract type, t must resolve to the same CompoundType name *)
          failwith "todo abstract type"
        | None ->  ES.throw @@ Error.make l @@ "unknown type '" ^ name ^ "' , should not happen"
        end
    end

  | CompoundType _, _ | _, CompoundType _ ->  ES.throw (Error.make l "todocompoundtype")



  | Box _at, Box _mt -> ES.throw (Error.make l "todo box")
  | RefType (at,am), RefType (mt,mm) -> if am <> mm then ES.throw (Error.make l "different mutability") else aux at mt g alias_checked
  | at,GenericType gt ->
    begin
      if List.mem gt generics then
        match List.assoc_opt gt g with
        | None -> return (at,(gt,at)::g)
        | Some t -> if t = at then return (at,g) else ES.throw (Error.make l "generic type mismatch")
      else
        ES.throw @@ Error.make l (Printf.sprintf "generic type %s not declared" gt)
    end
  | _ ->  ES.throw @@ Error.make l @@ Printf.sprintf "wants %s but %s provided" 
                                      (string_of_sailtype (Some m_param))
                                      (string_of_sailtype (Some arg))
  in aux arg m_param resolved_generics [] 


let check_binop op l r : sailtype ES.t = 
  let open MonadSyntax(ES) in
  match op with
  | Lt | Le | Gt | Ge | Eq | NEq ->
    let+ _ = matchArgParam r (snd l) [] [] in Bool
  | And | Or -> 
    let+ _ = matchArgParam l Bool [] [] 
    and* _ = matchArgParam r Bool [] [] in Bool
  | Plus | Mul | Div | Minus | Rem -> 
    let+ _ = matchArgParam r (snd l) [] [] in snd l


let check_call (name:string) (args: expression list) loc : sailtype option ES.t =
  let* m_env = ES.get_decl name (Self Method) in
  let* p_env = ES.get_decl name (Self Process) in
  match m_env,p_env  with
  | Some (_l,_,f), _ | _,Some (_l,f) -> 
    begin
      (* if variadic, we just make sure there is at least minimum number of arguments needed *)
      let args = if f.variadic then List.filteri (fun i _ -> i < (List.length f.args)) args else args in
      let nb_args = List.length args and nb_params = List.length f.args in
      let* () = ES.throw_if (nb_args <> nb_params)
        (Error.make loc (Printf.sprintf "unexpected number of arguments passed to %s : expected %i but got %i" name nb_params nb_args))
      in
      let* resolved_generics = List.fold_left2 
      (
        fun g (ca:expression) ({ty=a;_}:param) ->
          let* g in 
          let+ x = matchArgParam ca.info a f.generics g in
          snd x
      ) (return []) args f.args
      in
      begin
        match f.ret with
        | Some r ->  let+ r = degenerifyType r resolved_generics loc in Some r
        | None -> return None
      end
    end

  | None,None -> failwith @@ "Method '" ^ name ^ "' not found, HIR broken ? "



let find_function_source (fun_loc:loc) (_var: string option) (head_loc,id:loc*string) (import:(loc * string) option) (_el: expression list) : (import * SailModule.Declarations.method_decl)  ES.t =
  match import with
  | Some (loc,mname) -> 
      let+ f = 
      if mname = "_self" then 
        let* decl = ES.get_decl id (Self Method) in
        ES.throw_if_none decl (Error.make loc @@ "no function named " ^ id ^ " in current module ") 
      else
        let* env = ES.get in
        ES.throw_if_none (List.find_opt (fun m -> mname = m.mname) (THIREnv.get_imports env))
                         (Error.make loc @@ "unknown module " ^ mname) >>
        ES.throw_if_none (THIREnv.get_decl env id (Specific (mname,Method)))
                         (Error.make head_loc @@ "function "  ^ id ^ " not found in module " ^ mname)
      in
      {mname;loc;dir=""},f
  | None -> (* we must find where the function is defined *)
    begin
      let* decl = ES.get_decl id (All Method) in
      match decl with
      | [i,m] -> 
        Logs.debug (fun m -> m "resolved '%s' to %s" id i.mname);
        return (i,m)

      | [] ->  ES.throw @@ Error.make fun_loc @@ "unknown function " ^ id

      | _ as _x -> ES.throw @@ Error.make fun_loc @@ "multiple definition for function " ^ id ^ ", specify one with '::' annotation"
    end



    (*fixme : code duplication *)
  let find_type_source (loc,id: loc * string) (import : string option): (string * ty_defn)  ES.t =
    match import with
    | Some name -> 
      begin
        if name = "_self" then 
          begin
            let* decl = ES.get_decl id (Self Type) in
            let+ decl = ES.throw_if_none decl (Error.make loc @@ "no type named " ^ id ^ " in current module ") in
            name,decl
          end
        else
          let* env = ES.get in
          let+ t = 
            ES.throw_if_none (List.find_opt (fun {mname;_} -> mname = name) (THIREnv.get_imports env))
                              (Error.make loc @@ "unknown module " ^ name)  >> 
            ES.throw_if_none (THIREnv.get_decl env id (Specific (name,Type)))
                              (Error.make loc @@ "type "  ^ id ^ " not found in module " ^ name)
          in
          name,t
      end
    | None -> (* we must find where the function is defined *)
      begin
        let* decl = ES.get_decl id (All Type) in
        match decl with
        | [i,m] -> 
          Logs.debug (fun m -> m "resolved '%s' to %s" id i.mname);
          return (i.mname,m)
  
        | [] ->  ES.throw @@ Error.make loc @@ "unknown type " ^ id
  
        | _ as _x -> ES.throw @@ Error.make loc @@ "multiple definition for type " ^ id ^ ", specify one with '::' annotation"
      end
  

let resolve_type : sailtype -> sailtype ES.t = function
| CompoundType (mod_loc,id,l) -> 
  let+ mname,_ = find_type_source id mod_loc  in CompoundType (Some mname,id,l)
| _ as t ->  return t

