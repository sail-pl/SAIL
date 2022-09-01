open Common
open Pass
open TypesCommon
open IrHir
open Error
open Monad
open AstHir

module E = Logger

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
  let throw e = E.throw e |> lift
  let log e = E.log e |> lift
  let log_if b e = E.log_if b e |> lift
  let throw_if b e = E.throw_if b e |> lift
  let run e = E.bind e (fun e -> fst e |> E.pure)
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


let check_call (name:string) (args: expression list) loc : sailtype option ES.t =
  let* env = ES.get in
  match THIREnv.get_method env name,THIREnv.get_process env name  with
  | Some (_l,f), _ | _,Some (_l,f) -> 
    begin
      (* if variadic, we just make sure there is at least minimum number of arguments needed *)
      let args = if f.variadic then List.filteri (fun i _ -> i < (List.length f.args)) args else args in
      let nb_args = List.length args and nb_params = List.length f.args in
      let* () = ES.log_if (nb_args <> nb_params)
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


module Pass = Pass.MakeFunctionPass(V)(
struct
  let name = "THIR"
  
  type in_body = Hir.Pass.out_body
  type out_body = statement

  let rec lower_lexp (generics : string list) (e : Hir.expression) : expression ES.t = 
  let rec aux (e:Hir.expression) : expression ES.t = 
    match e with
    | Variable (l,id) -> 
      let* v = ES.get in 
      begin
        match THIREnv.get_var v id with
        | Some (_,(_,t)) -> return @@ Variable ((l,t),id)
        | None -> ES.throw @@ Error.make l (Printf.sprintf "unknown variable %s" id)
      end
    | Deref (l,e) -> let* e = lower_rexp generics e  in
      begin
        match e with
        | Ref _ as t -> return @@ Deref((l,extract_exp_loc_ty t |> snd), e)
        | _ -> ES.throw (Error.make l "can't deref a non-reference!")
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
            | Literal ((l,_),LInt n) ->
              ES.throw_if (n < 0 || n >= size) 
              (Error.make l @@ Printf.sprintf "index out of bounds : must be between 0 and %i (got %i)" (size - 1) n)
            | _ -> return ()
          end in return @@ ArrayRead ((l,t),array_exp,idx)
        | _ ->  ES.throw (Error.make l "not an array !")
      end
    | StructRead (l,_,_) | StructAlloc (l,_,_) | EnumAlloc (l,_,_) -> ES.throw (Error.make l "todo")
    | _ -> let l = extract_exp_loc_ty e in ES.throw (Error.make l "not a lvalue !")

    in aux e
  and lower_rexp (generics : string list) (e : Hir.expression) : expression ES.t =
  let rec aux (e:Hir.expression) : expression ES.t = match e with
  | Variable (l,id) -> 
    let* v = ES.get in 
    begin
      match THIREnv.get_var v id with
      | Some (_,(_,t)) -> return @@ Variable ((l,t),id)
      | None -> ES.throw @@ Error.make l (Printf.sprintf "unknown variable %s" id)
    end
  | Literal (l,li) -> let t = sailtype_of_literal li in return @@ Literal ((l,t),li)
  | UnOp (l,op,e) -> let+ e = aux e in UnOp ((l, extract_exp_loc_ty e |> snd),op,e)
  | BinOp (l,op,le,re) ->
    let* le = aux le and* re = aux re in
    let lt = extract_exp_loc_ty le  and rt = extract_exp_loc_ty re in
    let+ t = check_binop op lt rt |> E.recover (snd lt) |> ES.lift in 
    BinOp ((l,t),op,le,re)

  | Ref  (l,mut,e) -> let+ e = lower_lexp generics e in 
    let t = RefType (extract_exp_loc_ty e |> snd,mut) in
    Ref((l,t),mut, e)
  | ArrayStatic (l,el) -> 
    let* first_t = aux (List.hd el)  in
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
  | EnumAlloc _ -> let l = extract_exp_loc_ty e in ES.throw (Error.make l "enum alloc is not a rvalue !")
  | StructRead _ ->  let l = extract_exp_loc_ty e in ES.throw (Error.make l "todo struct read")


  in aux e


  let lower_function (decl:in_body function_type) (env:THIREnv.t) : out_body E.t = 
    let log e = let+ () = ES.log e in Skip dummy_pos in 
    let rec aux (s:in_body) : out_body ES.t = 
      let open MonadOperator(MonadOption.M) in
      match s with
      | DeclVar (l, mut, id, t, (optexp : Hir.expression option)) -> 
        let optexp = MonadOption.M.fmap (lower_rexp decl.generics) optexp in 
        begin
          let* var_type =
            match (t,optexp) with
            | (Some t,Some e) -> let* e in let tv = extract_exp_loc_ty e in let+ a = matchArgParam tv t decl.generics [] |> ES.lift in fst a
            | (Some t, None) -> return t
            | (None,Some t) -> let+ t in extract_exp_loc_ty t |> snd
            | (None,None) -> ES.throw (Error.make l "can't infere type with no expression")
            
          in
          let* () = ES.update (fun st -> THIREnv.declare_var st id (l,(mut,var_type)) ) in 
          match optexp with
          | None -> return (DeclVar (l,mut,id,Some var_type,None))
          | Some e -> let+ e in DeclVar (l,mut,id,Some var_type,Some e)
        end
        
      | Assign(l, e1, e2) -> 
        let* e1 = lower_lexp decl.generics e1
        and* e2 = lower_rexp decl.generics e2 in
        let* _ = matchArgParam (extract_exp_loc_ty e2) (extract_exp_loc_ty e1 |> snd) [] [] |> ES.lift in
        return (Assign(l, e1, e2))

      | Seq(l, c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        Seq(l, c1, c2) 


      | If(l, cond_exp, then_s, else_s) -> 
        let* cond_exp = lower_rexp decl.generics cond_exp in
        let* _ = matchArgParam (extract_exp_loc_ty cond_exp) Bool [] [] |> ES.lift in
        let* res = aux then_s in
        begin
        match else_s with
        | None -> return (If(l, cond_exp, res, None))
        | Some s -> let+ s = aux s in If(l, cond_exp, res, Some s)
        end

      | While(l,e,c) -> 
        let* e = lower_rexp decl.generics e in
        let+ t = aux c in
        While(l,e,t)

      | Break l -> return (Break l)

      | Case(l, e, _cases) ->
        let+ e = lower_rexp decl.generics e in
        Case (l, e, [])


      | Invoke (l, var, id, el) -> (* todo: handle var *) fun e ->
        let open MonadSyntax(E) in
        let* el,e' = listMapM (lower_rexp decl.generics) el e in 
        let+ _ = check_call id el l e' in Invoke(l, var, id,el),e'

      | Return (l, None) as r -> 
        if decl.ret = None then return r else log (Error.make l @@ Printf.sprintf "void return but %s returns %s" decl.name (string_of_sailtype decl.ret))

      | Return( l, Some e) ->
        if decl.bt <> Pass.BMethod then 
          log (Error.make l @@ Printf.sprintf "process %s : processes can't return non-void type" decl.name)
        else
          let* e = lower_rexp decl.generics e in
          let _,t as lt = extract_exp_loc_ty e in 
          begin
          match decl.ret with 
          | None -> 
            log (Error.make l @@ Printf.sprintf "returns %s but %s doesn't return anything"  (string_of_sailtype (Some t)) decl.name)
          | Some r ->
            let+ _ = matchArgParam lt r decl.generics [] |> ES.lift  in
            Return(l, Some e)
          end

      | Block (l, c) ->
          let* () = ES.update (fun e -> THIREnv.new_frame e |> E.pure) in
          let* res = aux c in 
          let+ () =  ES.update (fun e -> THIREnv.pop_frame e |> E.pure) in
          Block(l,res)

      | Skip l -> return (Skip l)
      | Watching (l, s, c) -> let+ res = aux c in Watching (l, s, res)
      | Emit (l, s) -> return (Emit (l,s))
      | Await (l, s) -> return (When (l, s, Skip l))
      | When (l, s, c) -> let+ res = aux c in When (l, s, res)
      | Run (l, id, el) -> fun e ->
        let open MonadSyntax(E) in
        let* el,e = listMapM (lower_rexp decl.generics) el e in
        let+ _ = check_call id el l e in
        Run (l, id, el),e

      | Par (l, c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        Par (l, c1, c2)

      | DeclSignal (l, s) -> return (DeclSignal (l, s))


    in 
    ES.run (aux decl.body env) |> Logger.recover (Skip dummy_pos)
  end
)