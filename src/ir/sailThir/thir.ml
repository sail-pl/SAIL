open Common
open Pass
open TypesCommon
open IrHir
open Error
open Monad
open AstHir

module E = MonadError

module V = (
  struct 
    type t = bool * sailtype
    let string_of_var (_,t) = string_of_sailtype (Some t)
    let to_var _ (m:bool) (t:sailtype) = m,t
  end
)

module THIREnv = SailModule.SailEnv(V)

module ES = struct
  include MonadState.T(E)(THIREnv)
  let error e = Result.error e |> lift
end

open MonadSyntax(ES)
open MonadFunctions(ES)


type expression = (loc * sailtype) AstHir.expression

type statement = expression AstHir.statement

let extract_exp_loc_ty : 'a AstHir.expression -> 'a = function
| Variable (lt,_) | Deref (lt,_) | StructRead (lt,_,_)
| ArrayRead (lt,_,_) | Literal (lt,_) | UnOp (lt,_,_)
| BinOp (lt,_,_,_) | Ref  (lt,_,_) | ArrayStatic (lt,_)
| StructAlloc (lt,_,_) | EnumAlloc  (lt,_,_) -> lt

let extract_statements_loc : _ AstHir.statement -> loc  = function
| Watching(l, _, _) | Emit(l, _) | Await(l, _)
| When(l, _, _)  | Run(l, _, _) | Par(l, _, _)
| DeclSignal(l, _)  | Skip (l)  | Return (l,_)
| Invoke (l,_,_,_) | Block (l, _) | If (l,_,_,_)
| DeclVar (l,_,_,_,_) | Seq (l,_,_) | Assign (l,_,_)
| While (l,_,_) | Break (l) | Case (l,_,_) -> l


let degenerifyType (t: sailtype) (generics: sailtype dict) loc : sailtype ES.t =
  let rec aux = function
  | Bool -> ES.pure Bool
  | Int -> ES.pure Int 
  | Float -> ES.pure Float
  | Char -> ES.pure Char
  | String -> ES.pure String
  | ArrayType (t,s) -> let+ t = aux t in ArrayType (t, s)
  | CompoundType (_name, _tl)-> ES.error [ loc ,"todo compoundtype"]
  | Box t -> let+ t = aux t in Box t
  | RefType (t,m) -> let+ t = aux t in RefType (t,m)
  | GenericType t when generics = [] -> ES.error [loc,Printf.sprintf "generic type %s present but empty generics list" t]
  | GenericType n -> 
    begin
      match List.assoc_opt n generics with
      | Some GenericType t -> GenericType t |> ES.pure
      | Some t -> aux t
      | None -> ES.error [loc,Printf.sprintf "generic type %s not present in the generics list" n]
    end
  in
  aux t

  
let matchArgParam (l,arg: loc * sailtype) (m_param : sailtype) (generics : string list) (resolved_generics: sailtype dict) : (sailtype * sailtype dict) E.t =
  let open MonadSyntax(E) in
  let rec aux (a:sailtype) (m:sailtype) (g: sailtype dict) = 
  match (a,m) with
  | Bool,Bool -> E.pure (Bool,g)
  | Int,Int -> E.pure (Int,g)
  | Float,Float -> E.pure (Float,g)
  | Char,Char -> E.pure (Char,g)
  | String,String -> E.pure (String,g)
  | ArrayType (at,s),ArrayType (mt,s') -> 
    if s = s' then
      let+ t,g = aux at mt g in ArrayType (t,s),g
    else
      Result.error [l,Printf.sprintf "array length mismatch : wants %i but %i provided" s' s]
  | CompoundType _, CompoundType _ -> Result.error [l, "todocompoundtype"]
  | Box _at, Box _mt -> Result.error [l,"todobox"]
  | RefType (at,am), RefType (mt,mm) -> if am <> mm then Result.error [l, "different mutability"] else aux at mt g
  | at,GenericType gt ->
    begin
      if List.mem gt generics then
        match List.assoc_opt gt g with
        | None -> E.pure (at,(gt,at)::g)
        | Some t -> if t = at then E.pure (at,g) else Result.error [l,"generic type mismatch"]
      else
        Result.error [l,Printf.sprintf "generic type %s not declared" gt]
    end
  | _ -> Result.error [l,Printf.sprintf "wants %s but %s provided" 
          (string_of_sailtype (Some m_param))
          (string_of_sailtype (Some arg))]
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


let check_call (name:string) (args: expression list) loc : sailtype option ES.t =
  let* env = ES.get in
  match THIREnv.get_method env name with
  | Some (_l,f) -> 
    begin
      (* if variadic, we just make sure there is at least minimum number of arguments needed *)
      let args = if f.variadic then List.filteri (fun i _ -> i < (List.length f.args)) args else args in
      let nb_args = List.length args and nb_params = List.length f.args in
      let* () = if nb_args <> nb_params 
        then 
          ES.error [loc, Printf.sprintf "unexpected number of arguments passed to %s : expected %i but got %i" name nb_params nb_args] 
        else ES.pure ()
      in
      let* resolved_generics = List.fold_left2 
      (
        fun g ca {ty=a;_} ->
          let* g in 
          let+ x = matchArgParam (extract_exp_loc_ty ca) a f.generics g |> ES.lift in
          snd x
      ) (ES.lift (Result.ok [])) args f.args
      in
      (* List.iter (fun (s,r) -> Printf.fprintf stdout "generic %s resolved to %s\n" s (string_of_sailtype (Some r)) ) resolved_generics; *)
      begin
        match f.ret with
        | Some r ->  let+ r = degenerifyType r resolved_generics loc in Some r
        | None -> None |> ES.pure
      end
    end

  | None -> ES.error [loc,"unknown method " ^ name] 


module Pass = Pass.MakeFunctionPass(V)(
struct
  type in_body = Hir.Pass.out_body
  type out_body = statement

  let rec lower_lexp (generics : string list) (e : Hir.expression) : expression ES.t = 
  let rec aux (e:Hir.expression) : expression ES.t = 
    match e with
    | Variable (l,id) -> 
      let* v = ES.get in 
      begin
        match THIREnv.get_var v id with
        | Some (_,(_,t)) -> Variable((l,t),id) |> ES.pure
        | None -> Result.error [l, Printf.sprintf "unknown variable %s" id] |> ES.lift
      end
    | Deref (l,e) -> let* e = lower_rexp generics e  in
      begin
        match e with
        | Ref _ as t -> Deref((l,extract_exp_loc_ty t |> snd), e) |> ES.pure
        | _ -> Result.error [l,"can't deref a non-reference!"] |> ES.lift
      end
    | ArrayRead (l,array_exp,idx) -> let* array_exp = aux array_exp and* idx = lower_rexp generics idx in
      begin 
        match extract_exp_loc_ty array_exp |> snd with
        | ArrayType (t,size) -> 
          let* _ = matchArgParam (extract_exp_loc_ty idx) Int generics [] |> ES.lift in
          let* () = 
          begin 
            (* can do a simple oob check if the type is an int literal *)
            match idx with
            | Literal ((l,_),LInt n) -> if n < 0 || n >= size then 
              Result.error [l, Printf.sprintf "index out of bounds : must be between 0 and %i (got %i)" (size - 1) n] |> ES.lift 
              else () |> ES.pure
            | _ -> () |> ES.pure
          end in
          ArrayRead((l,t),array_exp,idx) |> ES.pure
        | _ -> Result.error [l,"not an array !"] |> ES.lift
      end
    | StructRead (l,_,_) | StructAlloc (l,_,_) | EnumAlloc (l,_,_) -> Result.error [l, "todo"] |> ES.lift
    | _ -> let l = extract_exp_loc_ty e in Result.error [l, "not a lvalue !"] |> ES.lift

    in aux e
  and lower_rexp (generics : string list) (e : Hir.expression) : expression ES.t =
  let rec aux (e:Hir.expression) : expression ES.t = match e with
  | Variable (l,id) -> 
    let* v = ES.get in 
    begin
      match THIREnv.get_var v id with
      | Some (_,(_,t)) -> Variable((l,t),id) |> ES.pure
      | None -> Result.error [l, Printf.sprintf "unknown variable %s" id] |> ES.lift
    end
  | Literal (l,li) -> let t = sailtype_of_literal li in Literal((l,t),li) |> ES.pure
  | UnOp (l,op,e) -> let+ e = aux e in UnOp ((l, extract_exp_loc_ty e |> snd),op,e)
  | BinOp (l,op,le,re) ->
    let* le = aux le and* re = aux re in
    let lt = extract_exp_loc_ty le  and rt = extract_exp_loc_ty re in
    let+ t = check_binop op lt rt |> ES.lift in 
    BinOp ((l,t),op,le,re)

  | Ref  (l,mut,e) -> let+ e = lower_lexp generics e in Ref((l,RefType(extract_exp_loc_ty e |> snd,mut)),mut, e)
  | ArrayStatic (l,el) -> 
    let* first_t = List.hd el |> aux  in
    let first_t = extract_exp_loc_ty first_t |> snd in
    let* el = listMapM (
      fun e -> let+ e = aux e in
      let lt = extract_exp_loc_ty e in
      let+ _ = matchArgParam lt first_t [] [] |> ES.lift in e
    ) el in 
    let+ el = sequence el in
    let t = ArrayType (first_t, List.length el) in ArrayStatic((l,t),el)
  | ArrayRead _ -> lower_lexp generics e  (* todo : some checking *)
  | Deref _ -> lower_lexp generics e  (* todo : some checking *)
  | StructAlloc _ 
  | EnumAlloc _ -> let l = extract_exp_loc_ty e in Result.error [l, "not a rvalue !"] |> ES.lift
  | StructRead _ ->  let l = extract_exp_loc_ty e in Result.error [l, "todo struct read"] |> ES.lift


  in aux e


  let lower_function (decl:in_body function_type) (env:THIREnv.t) : out_body Error.result = 
    let rec aux (s:in_body) : out_body ES.t = 
      let open MonadOperator(MonadOption.M) in
      match s with
      | DeclVar (l, mut, id, t, (optexp : Hir.expression option)) -> 
        let optexp = MonadOption.M.fmap (lower_rexp decl.generics) optexp in 
        begin
          let* var_type =             
            match (t,optexp) with
            | (Some t,Some e) -> let* e in let tv = extract_exp_loc_ty e in let+ a = matchArgParam tv t decl.generics [] |> ES.lift in fst a
            | (Some t, None) -> ES.pure t
            | (None,Some t) -> let+ t in extract_exp_loc_ty t |> snd
            | (None,None) -> ES.error[l,"can't infere type with no expression"]
            
          in
          let* () = ES.update (fun st -> THIREnv.declare_var st id (l,(mut,var_type)) ) in 
          match optexp with
          | None -> DeclVar (l,mut,id,Some var_type,None) |> ES.pure
          | Some e -> let+ e in DeclVar (l,mut,id,Some var_type,Some e)
        end
        
      | Assign(loc, e1, e2) -> 
        let* e1 = lower_lexp decl.generics e1
        and* e2 = lower_rexp decl.generics e2 in
        let* _ = matchArgParam (extract_exp_loc_ty e2) (extract_exp_loc_ty e1 |> snd) [] [] |> ES.lift in
        Assign(loc, e1, e2) |> ES.pure

      | Seq(loc, c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        Seq(loc, c1, c2) 


      | If(loc, cond_exp, then_s, else_s) -> 
        let* cond_exp = lower_rexp decl.generics cond_exp in
        let* _ = matchArgParam (extract_exp_loc_ty cond_exp) Bool [] [] |> ES.lift in
        let* res = aux then_s in
        begin
        match else_s with
        | None -> If(loc, cond_exp, res, None) |> ES.pure
        | Some s -> let+ s = aux s in If(loc, cond_exp, res, Some s)
        end

      | While(loc,e,c) -> 
        let* e = lower_rexp decl.generics e in
        let+ t = aux c in
        While(loc,e,t)

      | Break(l) -> Break(l) |> ES.pure

      | Case(loc, e, _cases) ->
        let+ e = lower_rexp decl.generics e  in
        Case (loc, e, [])


      | Invoke(loc, var, id, el) -> (* todo: handle var *) fun e ->
        let open MonadSyntax(E) in
        let* el,e' = listMapM (lower_rexp decl.generics) el e in 
        let+ _ = check_call id el loc e' in Invoke(loc, var, id,el),e'

      | Return(l, None) as r -> 
        if decl.ret = None then r |> ES.pure else ES.error [l,"void return"] 

      | Return(l, Some e) ->
        if decl.bt <> Pass.BMethod then 
          ES.error [l, Printf.sprintf "process %s : processes can't return non-void type" decl.name]
        else
          begin
          match decl.ret with 
          | None -> ES.error [l,"non-void return"]
          | Some r ->
            let* e = lower_rexp decl.generics e in
            let+ _ = matchArgParam (extract_exp_loc_ty e) r decl.generics [] |> ES.lift in
            Return(l, Some e)
          end

      | Block (loc, c) ->
          let* () = ES.update (fun e -> THIREnv.new_frame e |> E.pure) in
          let* res = aux c in 
          let+ () =  ES.update (fun e -> THIREnv.pop_frame e |> E.pure) in
          Block(loc,res)

      | Skip (loc) -> Skip(loc) |> ES.pure

      | s when decl.bt = Pass.BMethod -> 
        ES.error [extract_statements_loc s, Printf.sprintf "method %s : methods can't contain reactive statements" decl.name]


      | Watching(loc, s, c) -> let+ res = aux c in Watching(loc, s, res)
      | Emit(loc, s) -> Emit(loc,s) |> ES.pure
      | Await(loc, s) -> When(loc, s, Skip(loc)) |> ES.pure
      | When(loc, s, c) -> let+ res = aux c in When(loc, s, res)
      | Run(loc, id, el) -> fun e ->
        let open MonadSyntax(E) in
        let* el,e = listMapM (lower_rexp decl.generics) el e in
        let+ _ = check_call id el loc e in
        Run(loc, id, el),e

      | Par(loc, c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        Par(loc, c1, c2)

      | DeclSignal(loc, s) -> DeclSignal(loc, s) |> ES.pure


    in 
    Logs.debug (fun m -> m "lowering to THIR %s" decl.name);
    let open MonadSyntax(E) in
    let+ res = aux decl.body env in fst res
  end
)