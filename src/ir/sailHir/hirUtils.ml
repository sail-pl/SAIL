open Common
open TypesCommon
open Monad


type expression = (loc,l_str option) AstHir.expression
type statement = (loc,l_str option,expression) AstHir.statement

module M = HirMonad.Make( struct
  type t = statement
  let mempty : t = {info=dummy_pos; stmt=Skip}
  let mconcat : t -> t -> t = fun x y -> {info=dummy_pos; stmt=Seq (x,y)}
  end)

open M
open MonadSyntax(M.E)
open MonadOperator(M.E)
module D = SailModule.DeclEnv

let find_compound_type_source (loc,id: l_str) (import : l_str option) (env : D.t) : (l_str * D.decls)  E.t =
let filt = [E (); S (); T ()] in (* a compoundtype can't point to a method / process *)
match import with
| Some (iloc,name) -> 
  begin
    if name = Constants.sail_module_self || name = D.get_name env then 
      begin
        let+ decl = 
          D.find_decl id (Self (Filter filt)) env 
          |> E.throw_if_none (Error.make loc @@ "no declaration named '" ^ id ^ "' in current module ")
        in
        (iloc,D.get_name env),decl
      end
    else
      let+ t = 
        E.throw_if_none (Error.make iloc  ~hint:(Some (None,Fmt.str "try importing the module with 'import %s'" name)) @@ "unknown module " ^ name)  
                        (List.find_opt (fun {mname;_} -> mname = name) (D.get_imports env)) >> 
        E.throw_if_none (Error.make loc @@ "declaration "  ^ id ^ " not found in module " ^ name)
                        (D.find_decl id (Specific (name, Filter filt)) env)                          
      in
      (iloc,name),t
  end
| None -> (* find it ourselves *)
  begin
    let decl = D.find_decl id (All (Filter filt)) env in
    match decl with
    | [i,m] -> 
      Logs.debug (fun m -> m "'%s' is from %s" id i.mname);
      return ((dummy_pos,i.mname),m)

    | [] ->  E.throw @@ Error.make loc @@ "unknown declaration " ^ id

    | _ as choice -> E.throw 
                  @@ Error.make loc ~hint:(Some (None,"specify one with '::' annotation")) 
                  @@ Fmt.str "multiple definitions for declaration %s : \n\t%s" id 
                     (List.map (fun (i,def) -> match def with T def -> Fmt.str "from %s : %s" i.mname (string_of_sailtype (def.ty)) | _ -> "") choice |> String.concat "\n\t")
  end


let follow_type ty env : (sailtype * D.t) E.t = 
  
  let current = SailModule.DeclEnv.get_name env in

  Logs.debug (fun m -> m "following type '%s'" (string_of_sailtype (Some ty)));

  let rec aux ty' path : (sailtype * ty_defn list) E.t = 
    match ty' with 
    | CompoundType {origin;name=id;generic_instances;_} -> (* compound type, find location and definition *) 
      let* (l,origin),def = find_compound_type_source id origin env in 
      let default = fun ty -> CompoundType {origin=Some (l,origin);name=id; generic_instances;decl_ty=Some ty} in 
      if origin <> current then return (default (T ()),path)
      else
        begin
          match def with
          | T def ->
            begin
            match def.ty with 
            | Some ty -> 
              (* new type to follow, but check for circular dep first *)
              E.throw_if_some ( fun _ -> Error.make def.loc 
                                        @@ Fmt.str "circular type declaration : %s" 
                                        @@ String.concat " -> " (List.rev (def::path) |> List.map (fun ({name;_}:ty_defn) -> name))
                              ) 
                              (List.find_opt (fun (d:ty_defn) -> d.name = def.name) path) 
              >> aux ty (def::path)

            | None -> (* abstract type *) 
              Logs.debug (fun m -> m "'%s' resolves to abstract type '%s' " (string_of_sailtype (Some ty)) def.name); 
              return (default (T ()),path)
            end
          | _ -> return (default (unit_decl_of_decl def),path) (* must point to an enum or struct, nothing to resolve *)
          end
    | ArrayType (t,n) -> let+ t,path = aux t path in  ArrayType (t,n),path
    | Box t -> let+ t,path = aux t path in Box t,path
    | RefType (t,mut) -> let+ t,path = aux t path in RefType (t,mut),path
    | Bool | Char | Int | Float | String | GenericType _ as t ->  (* basic type, stop *)
      Logs.debug (fun m -> m "'%s' resolves to '%s'" (string_of_sailtype (Some ty)) (string_of_sailtype (Some ty')));
      return (t,path)
  in
  let+ res,p = aux ty [] in
  (* p only contains type_def from the current module *)
  let env = List.fold_left (fun env (td:ty_defn) -> D.update_decl td.name {td with ty=Some res} (Self Type) env) env p in 
  res,env