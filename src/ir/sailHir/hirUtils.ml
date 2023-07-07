open Common
open TypesCommon
open Monad


type expression = (loc,l_str option) AstHir.expression
type statement = (loc,l_str option,expression) AstHir.statement

module M = HirMonad.Make( struct
  type t = statement
  let mempty : t = {info=dummy_pos; stmt=Skip}
  let mconcat : t -> t -> t = fun x y -> {info=dummy_pos; stmt=Seq (x,y)}
  end
)

open M
open MonadSyntax(M.E)
open MonadOperator(M.E)
open MonadFunctions(M.E)
module D = SailModule.DeclEnv

let find_symbol_source ?(filt = [E (); S (); T ()] ) (loc,id: l_str) (import : l_str option) (env : D.t) : (l_str * D.decls)  E.t =
match import with
| Some (iloc,name) -> 
  if name = Constants.sail_module_self || name = D.get_name env then 
      let+ decl = 
        D.find_decl id (Self (Filter filt)) env 
        |> E.throw_if_none (Error.make loc @@ "no declaration named '" ^ id ^ "' in current module ")
      in
      (iloc,D.get_name env),decl
  else
    let+ t = 
      E.throw_if_none (Error.make iloc  ~hint:(Some (None,Fmt.str "try importing the module with 'import %s'" name)) @@ "unknown module " ^ name)  
                      (List.find_opt (fun {mname;_} -> mname = name) (D.get_imports env)) >>=
     fun _ ->
      E.throw_if_none (Error.make loc @@ "declaration "  ^ id ^ " not found in module " ^ name)
                      (D.find_decl id (Specific (name, Filter filt)) env)
    in
    (iloc,name),t
| None -> (* find it ourselves *)
  begin
    let decl = D.find_decl id (All (Filter filt)) env in
    match decl with
    | [i,m] -> 
      (* [%log debug "'%s' is from %s" id i.mname); *)
      return ((dummy_pos,i.mname),m)

    | [] ->  E.throw @@ Error.make loc @@ "unknown declaration " ^ id

    | _ as choice -> E.throw 
                  @@ Error.make loc ~hint:(Some (None,"specify one with '::' annotation")) 
                  @@ Fmt.str "multiple definitions for declaration %s : \n\t%s" id 
                     (List.map (fun (i,def) -> match def with T def -> Fmt.str "from %s : %s" i.mname (string_of_sailtype (def.ty)) | _ -> "") choice |> String.concat "\n\t")
  end

let follow_type ty env : (sailtype * D.t) E.t = 
  
  let current = SailModule.DeclEnv.get_name env in

  (* [%log debug "following type '%s'" (string_of_sailtype (Some ty))); *)

  let rec aux ty' path : (sailtype * ty_defn list) E.t = 
    (* [%log debug "path: %s" (List.map (fun ({name;_}:ty_defn) -> name)path |> String.concat " ")); *)
    match ty' with 
    | CompoundType {origin;name=id;generic_instances;_} -> (* compound type, find location and definition *) 
      let* (l,origin),def = find_symbol_source id origin env in 
      let default = fun ty -> CompoundType {origin=Some (l,origin);name=id; generic_instances;decl_ty=Some ty} in 
      begin
        match def with
        | T def when origin=current ->
          begin
          match def.ty with 
          | Some ty -> (
            E.throw_if_some (fun _ -> (Error.make def.loc 
            @@ Fmt.str "circular type declaration : %s" 
            @@ String.concat " -> " (List.rev (def::path) |> List.map (fun ({name;_}:ty_defn) -> name))))
            (List.find_opt (fun (d:ty_defn) -> d.name = def.name) path)
            
            >>= (fun () -> aux ty (def::path))
            )
          | None -> (* abstract type *) 
            (* [%log debug "'%s' resolves to abstract type '%s' " (string_of_sailtype (Some ty)) def.name);  *)
            return (default (T ()),path)
          end
        | _ -> 
          return (default (unit_decl_of_decl def),path) (* must point to an enum or struct, nothing to resolve *)
        end
    | ArrayType (t,n) -> let+ t,path = aux t path in  ArrayType (t,n),path
    | Box t -> let+ t,path = aux t path in Box t,path
    | RefType (t,mut) -> let+ t,path = aux t path in RefType (t,mut),path
    | Bool | Char | Int _ | Float | String | GenericType _ as t ->  (* basic type, stop *)
      (* [%log debug "'%s' resolves to '%s'" (string_of_sailtype (Some ty)) (string_of_sailtype (Some ty'))); *)
      return (t,path)
  in
  let+ res,p = aux ty [] in
  (* p only contains type_def from the current module *)
  let env = List.fold_left (fun env (td:ty_defn) -> D.update_decl td.name {td with ty=Some res} (Self Type) env) env p in 
  res,env

let check_non_cyclic_struct (name:string) (l,proto) env : unit E.t = 
  let rec aux id curr_loc (s:struct_proto) checked = 
    let* () = E.throw_if 
                (Error.make l
                ~hint:(Some (Some curr_loc,"Hint : try boxing this type"))
                @@ Fmt.str "circular structure declaration : %s" 
                @@ String.concat " -> " (List.rev (id::checked))
                
                )
                
                (List.mem id checked) in 
    let checked = id::checked in 
    ListM.iter (
      fun (_,(l,t,_)) -> match t with

      | CompoundType {name=_,name;origin=Some (_,origin); decl_ty = Some S ();_} -> 
        begin
          match D.find_decl name (Specific (origin,(Filter [S ()]))) env with
          | Some (S (_,d)) -> aux name l d checked
          | _ -> failwith "invariant : all compound types must have a correct origin and type at this step"
        end
      | CompoundType {origin=None;decl_ty=None;_} -> E.throw (Error.make l "follow type not called")
      | _ -> return ()
    ) s.fields
  in
  aux name l proto []