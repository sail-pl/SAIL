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


type expression = ThirUtils.expression
type statement = ThirUtils.statement

module Pass = Pass.MakeFunctionPass(V)(
struct
  let name = "THIR"
  type in_body = Hir.Pass.out_body
  type out_body = statement

  let rec lower_lexp (generics : string list) (e : Hir.expression) : expression ES.t = 
  let rec aux (e:Hir.expression) : expression ES.t = 
    let loc = e.info in  match e.exp with
    | Variable id -> 
      let* v = ES.get_var id in 
      let+ (_,(_,t)) = ES.throw_if_none v (Error.make loc @@ Printf.sprintf "unknown variable %s" id) in
      buildExp (loc,t) @@ Variable id

    | Deref e -> let* e = lower_rexp generics e in
      (* return @@ Deref((l,extract_exp_loc_ty e |> snd), e) *)
      begin
        match e.exp with
        | Ref (_,r)  -> return @@ buildExp r.info @@ Deref e
        | _ -> return e
      end
    | ArrayRead (array_exp,idx) -> let* array_exp = aux array_exp and* idx = lower_rexp generics idx in
      begin 
        match snd array_exp.info with
        | ArrayType (t,size) -> 
          let* _ = matchArgParam (idx.info) Int generics [] in
          let* () = 
          begin 
            (* can do a simple oob check if the type is an int literal *)
            match idx.exp with
            | Literal (LInt n) ->
              ES.throw_if (n < 0 || n >= size) 
              (Error.make (fst idx.info) @@ Printf.sprintf "index out of bounds : must be between 0 and %i (got %i)" (size - 1) n)
            | _ -> return ()
          end in return @@ buildExp (loc,t) @@ ArrayRead (array_exp,idx)
        | _ ->  ES.throw (Error.make loc "not an array !")
      end
    | StructRead _ | StructAlloc _ | EnumAlloc _ -> ES.throw (Error.make e.info "todo")
    | _ -> ES.throw (Error.make loc "not a lvalue !")

    in aux e
  and lower_rexp (generics : string list) (e : Hir.expression) : expression ES.t =
  let rec aux (e:Hir.expression) : expression ES.t = 
    let loc = e.info in match e.exp with
    | Variable id -> 
      let* v = ES.get_var id in 
      let+ (_,(_,t)) = ES.throw_if_none v (Error.make loc @@ Printf.sprintf "unknown variable %s" id) in
      buildExp (loc,t) @@ Variable id
    | Literal li -> let t = sailtype_of_literal li in return @@ buildExp (loc,t) @@ Literal li
    | UnOp (op,e) -> let+ e = aux e in buildExp e.info @@ UnOp (op,e)
    | BinOp (op,le,re) ->
      let* le = aux le and* re = aux re in
      let lt = le.info  and rt = re.info in
      let+ t = check_binop op lt rt |> ES.recover (snd lt) in 
      buildExp (loc,t) @@ BinOp (op,le,re)

    | Ref (mut,e) -> let+ e = lower_lexp generics e in 
      let t = RefType (snd e.info,mut) in
      buildExp (loc,t) @@ Ref(mut, e)
    | ArrayStatic el -> 
      let* first_t = aux (List.hd el) in
      let first_t = snd first_t.info in
      let* el = listMapM (
        fun e -> let+ e = aux e in
        let+ _ = matchArgParam e.info first_t [] [] in e
      ) el in 
      let+ el = sequence el in
      let t = ArrayType (first_t, List.length el) in 
      buildExp (loc,t) (ArrayStatic el)

    | MethodCall ((l,_) as lid,source,el) -> 
      let* (el: expression list) = listMapM (lower_rexp generics) el in 
      let* mod_loc,(_,realname,m) = find_function_source e.info None lid source el in
      let+ ret = ES.throw_if_none m.ret  (Error.make e.info "methods in expressions should return a value") in
      buildExp (loc,ret) (MethodCall ((l,realname),mod_loc,el)) 


    | ArrayRead _ -> lower_lexp generics e  (* todo : some checking *)
    | Deref _ -> lower_lexp generics e  (* todo : some checking *)
    | StructAlloc _ 
    | EnumAlloc _ -> ES.throw (Error.make loc "enum alloc is not a rvalue !")
    | StructRead _ ->   ES.throw (Error.make loc "todo struct read")
  in aux e


  let lower_function (decl:in_body function_type) (env:THIREnv.t) _ : out_body E.t = 
    let log e = let+ () = ES.log e in buildStmt e.where Skip  in 
    let rec aux (s:in_body) : out_body ES.t = 
      let open MonadOperator(MonadOption.M) in
      let loc = s.info in
      match s.stmt with
      | DeclVar (mut, id, t, (optexp : Hir.expression option)) -> 
        let optexp = MonadOption.M.fmap (lower_rexp decl.generics) optexp in 
        begin
          let* var_type =
            match (t,optexp) with
            | (Some t,Some e) -> 
              let* t = resolve_type t in 
              let* e in let+ a = matchArgParam e.info t decl.generics [] in fst a
            | (Some t, None) -> resolve_type t
            | (None,Some t) -> let+ t in snd t.info
            | (None,None) -> ES.throw (Error.make loc "can't infere type with no expression")
            
          in
          let* var_type = resolve_type var_type in 
          let* () = ES.update (fun st -> THIREnv.declare_var st id (loc,(mut,var_type)) ) in 
          match optexp with
          | None -> return @@ buildStmt loc @@ DeclVar (mut,id,Some var_type,None)
          | Some e -> let+ e in buildStmt loc @@ DeclVar (mut,id,Some var_type,Some e)
        end
        
      | Assign(e1, e2) -> 
        let* e1 = lower_lexp decl.generics e1
        and* e2 = lower_rexp decl.generics e2 in
        let* _ = matchArgParam e2.info (snd e1.info) [] [] in
        return @@ buildStmt loc (Assign(e1, e2))

      | Seq(c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        buildStmt loc (Seq(c1, c2))


      | If(cond_exp, then_s, else_s) -> 
        let* cond_exp = lower_rexp decl.generics cond_exp in
        let* _ = matchArgParam cond_exp.info Bool [] [] in
        let* res = aux then_s in
        begin
        match else_s with
        | None -> return @@ buildStmt loc (If(cond_exp, res, None))
        | Some s -> let+ s = aux s in buildStmt loc (If(cond_exp, res, Some s))
        end

      | While(e,c) -> 
        let* e = lower_rexp decl.generics e in
        let+ t = aux c in
        buildStmt loc (While(e,t))

      | Break -> return (buildStmt loc Break)

      | Case(e, _cases) ->
        let+ e = lower_rexp decl.generics e in
        buildStmt loc (Case (e, []))


      | Invoke (var, mod_loc, id, el) -> (* todo: handle var *)
        let* el = listMapM (lower_rexp decl.generics) el in 
        let* mod_loc,_ = find_function_source s.info var id mod_loc el in 
        (* let+ _ = check_call (snd id) el loc in  *)
        buildStmt loc (Invoke(var,mod_loc, id,el)) |> return 

      | Return None as r -> 
        if decl.ret = None then return (buildStmt loc r) else 
          log (Error.make loc @@ Printf.sprintf "void return but %s returns %s" decl.name (string_of_sailtype decl.ret))

      | Return (Some e) ->
        if decl.bt <> Pass.BMethod then 
          log (Error.make loc @@ Printf.sprintf "process %s : processes can't return non-void type" decl.name)
        else
          let* e = lower_rexp decl.generics e in
          let _,t as lt = e.info in 
          begin
          match decl.ret with 
          | None -> 
            log (Error.make loc @@ Printf.sprintf "returns %s but %s doesn't return anything"  (string_of_sailtype (Some t)) decl.name)
          | Some r ->
            let+ _ = matchArgParam lt r decl.generics []  in
            buildStmt loc (Return (Some e))
          end

      | Block c ->
          let* () = ES.update (fun e -> THIREnv.new_frame e |> E.pure) in
          let* res = aux c in 
          let+ () =  ES.update (fun e -> THIREnv.pop_frame e |> E.pure) in
          buildStmt loc (Block res)

      | Skip -> return (buildStmt loc Skip)
      | Watching (s, c) -> let+ res = aux c in buildStmt loc (Watching (s, res))
      | Emit s -> return (buildStmt loc (Emit s))
      | Await s -> return (buildStmt loc (When (s, buildStmt loc Skip)))
      | When (s, c) -> let+ res = aux c in buildStmt loc (When (s, res))
      | Run (id, el) ->
        let* el = listMapM (lower_rexp decl.generics) el in
        (* let+ _ = check_call (snd id) el loc in *)
        buildStmt loc (Run (id, el)) |> return

      | Par (c1, c2) -> 
        let* env = ES.get in 
        let* c1 = aux c1 in
        let* () = ES.set env in
        let+ c2 = aux c2 in
        buildStmt loc (Par (c1, c2))

      | DeclSignal s -> return (buildStmt loc (DeclSignal s))


    in 
    ES.run (aux decl.body env) |> Logger.recover (buildStmt dummy_pos Skip)
  end
)