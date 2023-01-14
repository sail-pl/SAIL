open Common
open TypesCommon
open IrHir
open ThirMonad
open Monad

open MonadSyntax(ES)
open MonadFunctions(ES)

let extract_exp_loc_ty : 'a AstHir.expression -> 'a = function
| Variable (lt,_) | Deref (lt,_) | StructRead (lt,_,_)
| ArrayRead (lt,_,_) | Literal (lt,_) | UnOp (lt,_,_)
| BinOp (lt,_,_,_) | Ref  (lt,_,_) | ArrayStatic (lt,_)
| StructAlloc (lt,_,_) | EnumAlloc  (lt,_,_) -> lt

let extract_statements_loc : _ AstHir.statement -> loc  = function
| Watching(l, _, _) | Emit(l, _) | Await(l, _)
| When(l, _, _)  | Run(l, _, _) | Par(l, _, _)
| DeclSignal(l, _)  | Skip l  | Return (l,_)
| Invoke (l,_,_,_) | Block (l, _) | If (l,_,_,_)
| DeclVar (l,_,_,_,_) | Seq (l,_,_) | Assign (l,_,_)
| While (l,_,_) | Break l | Case (l,_,_) -> l


let degenerifyType (t: sailtype) (generics: sailtype dict) loc : sailtype ES.t =
  let rec aux = function
  | Bool -> return Bool
  | Int -> return Int 
  | Float -> return Float
  | Char -> return Char
  | String -> return String
  | ArrayType (t,s) -> let+ t = aux t in ArrayType (t, s)
  | CompoundType (_name, _tl)-> ES.throw (Error.make loc "todo compoundtype")
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

  
let matchArgParam (l,arg: loc * sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: sailtype dict) : (sailtype * sailtype dict) E.t =
  let open MonadSyntax(E) in
  let rec aux (a:sailtype) (m:sailtype) (g: sailtype dict) = 
  match (a,m) with
  | Bool,Bool -> return (Bool,g)
  | Int,Int -> return (Int,g)
  | Float,Float -> return (Float,g)
  | Char,Char -> return (Char,g)
  | String,String -> return (String,g)
  | ArrayType (at,s),ArrayType (mt,s') -> 
    if s = s' then
      let+ t,g = aux at mt g in ArrayType (t,s),g
    else
      E.throw @@ Error.make l (Printf.sprintf "array length mismatch : wants %i but %i provided" s' s)
  | CompoundType _, CompoundType _ -> E.throw (Error.make l "todocompoundtype")
  | Box _at, Box _mt -> E.throw (Error.make l "todo box")
  | RefType (at,am), RefType (mt,mm) -> if am <> mm then E.throw (Error.make l "different mutability") else aux at mt g
  | at,GenericType gt ->
    begin
      if List.mem gt generics then
        match List.assoc_opt gt g with
        | None -> return (at,(gt,at)::g)
        | Some t -> if t = at then return (at,g) else E.throw (Error.make l "generic type mismatch")
      else
        E.throw @@ Error.make l (Printf.sprintf "generic type %s not declared" gt)
    end
  | _ ->  E.throw @@ Error.make l @@ Printf.sprintf "wants %s but %s provided" 
                                      (string_of_sailtype (Some m_param))
                                      (string_of_sailtype (Some arg))
  in aux arg m_param resolved_generics  


let check_binop op l r : sailtype E.t = 
  let open MonadSyntax(E) in
  match op with
  | Lt | Le | Gt | Ge | Eq | NEq ->
    let+ _ = matchArgParam r (snd l) [] [] in Bool
  | And | Or -> 
    let+ _ = matchArgParam l Bool [] [] 
    and* _ = matchArgParam r Bool [] [] in Bool
  | Plus | Mul | Div | Minus | Rem -> 
    let+ _ = matchArgParam r (snd l) [] [] in snd l


let check_call (name:string) (args: 'a list) loc : sailtype option ES.t =
  let* env = ES.get in
  match THIREnv.get_method env name,THIREnv.get_process env name  with
  | Some (_l,f), _ | _,Some (_l,f) -> 
    begin
      (* if variadic, we just make sure there is at least minimum number of arguments needed *)
      let args = if f.variadic then List.filteri (fun i _ -> i < (List.length f.args)) args else args in
      let nb_args = List.length args and nb_params = List.length f.args in
      let* () = ES.throw_if (nb_args <> nb_params)
        (Error.make loc (Printf.sprintf "unexpected number of arguments passed to %s : expected %i but got %i" name nb_params nb_args))
      in
      let* resolved_generics = List.fold_left2 
      (
        fun g ca {ty=a;_} ->
          let* g in 
          let+ x = matchArgParam (extract_exp_loc_ty ca) a f.generics g |> ES.lift in
          snd x
      ) (return []) args f.args
      in
      begin
        match f.ret with
        | Some r ->  let+ r = degenerifyType r resolved_generics loc in Some r
        | None -> return None
      end
    end

  | None,None -> failwith "problem with hir"

