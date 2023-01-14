open Common
open Pass
open TypesCommon
open IrHir
open Error
open Monad
open AstHir

open ThirMonad
open ThirUtils

open MonadSyntax(ES)
open MonadFunctions(ES)


type expression = (loc * sailtype) AstHir.expression

type statement = expression AstHir.statement

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
        let+ _ = check_call (snd id) el l e' in Invoke(l, var, id,el),e'

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
        let+ _ = check_call (snd id) el l e in
        Run (l, id, el),e

      | Par (l, c1, c2) -> 
        let* env = ES.get in 
        let* c1 = aux c1 in
        let* () = ES.set env in
        let+ c2 = aux c2 in
        Par (l, c1, c2)

      | DeclSignal (l, s) -> return (DeclSignal (l, s))


    in 
    ES.run (aux decl.body env) |> Logger.recover (Skip dummy_pos)
  end
)