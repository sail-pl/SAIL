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
open MonadOperator(ES)


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
          matchArgParam (idx.info) Int generics [] >>
          begin 
            (* can do a simple oob check if the type is an int literal *)
            match idx.exp with
            | Literal (LInt n) ->
              ES.throw_if (n < 0 || n >= size) 
              (Error.make (fst idx.info) @@ Printf.sprintf "index out of bounds : must be between 0 and %i (got %i)" (size - 1) n)
            | _ -> return ()
          end >> return @@ buildExp (loc,t) @@ ArrayRead (array_exp,idx)
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
      let* le = aux le in
      let* re = aux re in
      let lt = le.info  and rt = re.info in
      let+ t = check_binop op lt rt |> ES.recover (snd lt) in 
      buildExp (loc,t) @@ BinOp (op,le,re)

    | Ref (mut,e) -> let+ e = lower_lexp generics e in 
      let t = RefType (snd e.info,mut) in
      buildExp (loc,t) @@ Ref(mut, e)
    | ArrayStatic el -> 
      let* first_t = aux (List.hd el) in
      let first_t = snd first_t.info in
      let* el = ListM.map (
        fun e -> let+ e = aux e in
        let+ _ = matchArgParam e.info first_t [] [] in e
      ) el in 
      let+ el = ListM.sequence el in
      let t = ArrayType (first_t, List.length el) in 
      buildExp (loc,t) (ArrayStatic el)

    | MethodCall ((l,name) as lid,source,el) -> 
      let* (el: expression list) = ListM.map (lower_rexp generics) el in 
      let* mod_loc,(_,_realname,m) = find_function_source e.info None lid source el in
      let+ ret = ES.throw_if_none m.ret  (Error.make e.info "methods in expressions should return a value") in
      buildExp (loc,ret) (MethodCall ((l,name),mod_loc,el)) 


    | ArrayRead _ -> lower_lexp generics e  (* todo : some checking *)
    | Deref _ -> lower_lexp generics e  (* todo : some checking *)
    | StructAlloc _ 
    | EnumAlloc _ -> ES.throw (Error.make loc "enum alloc is not a rvalue !")
    | StructRead _ ->   ES.throw (Error.make loc "todo struct read")
  in aux e


  let lower_function (decl:in_body function_type) (env:THIREnv.t) _ : (out_body * THIREnv.D.t) E.t = 
    let log_and_skip e = ES.log e >> return @@ buildStmt e.where Skip  
    in 

    let rec aux (s:in_body) : out_body ES.t = 
      let loc = s.info in
      let buildStmt = buildStmt loc in 
      match s.stmt with
      | DeclVar (mut, id, opt_t, (opt_exp : Hir.expression option)) -> 
        let* ((ty,opt_e):sailtype * 'b) =
          begin
            match opt_t,opt_exp with
            | Some t, Some e -> 
              let* e = lower_rexp decl.generics e in
              matchArgParam e.info t decl.generics [] >>
              return (t,Some e)
            | None,Some e -> 
              let+ e = lower_rexp decl.generics e in
              (snd e.info),Some e
            | Some t,None -> return (t,None)
            | None,None -> ES.throw (Error.make loc "can't infere type with no expression")
          end 
        in
        ES.update (fun st -> THIREnv.declare_var id (loc,(mut,ty)) st) >>
        return (buildStmt @@ DeclVar (mut,id,Some ty,opt_e))
        
        
      | Assign(e1, e2) -> 
        let* e1 = lower_lexp decl.generics e1
        and* e2 = lower_rexp decl.generics e2 in
        matchArgParam e2.info (snd e1.info) [] [] >>
        return @@ buildStmt (Assign(e1, e2))

      | Seq(c1, c2) -> 
        let* c1 = aux c1 in
        let+ c2 = aux c2 in
        buildStmt (Seq(c1, c2))


      | If(cond_exp, then_s, else_s) -> 
        let* cond_exp = lower_rexp decl.generics cond_exp in
        matchArgParam cond_exp.info Bool [] [] >>
        let* res = aux then_s in
        begin
        match else_s with
        | None -> return @@ buildStmt (If(cond_exp, res, None))
        | Some s -> let+ s = aux s in buildStmt (If(cond_exp, res, Some s))
        end

      | While(e,c) -> 
        let* e = lower_rexp decl.generics e in
        let+ t = aux c in
        buildStmt (While(e,t))

      | Break -> return (buildStmt Break)

      | Case(e, _cases) ->
        let+ e = lower_rexp decl.generics e in
        buildStmt (Case (e, []))


      | Invoke (var, mod_loc, id, el) -> (* todo: handle var *)
        let* el = ListM.map (lower_rexp decl.generics) el in 
        let* mod_loc,_ = find_function_source s.info var id mod_loc el in 
        (* let+ _ = check_call (snd id) el loc in  *)
        buildStmt (Invoke(var,mod_loc, id,el)) |> return 

      | Return None as r -> 
        if decl.ret = None then return (buildStmt r) else 
          log_and_skip (Error.make loc @@ Printf.sprintf "void return but %s returns %s" decl.name (string_of_sailtype decl.ret))

      | Return (Some e) ->
        if decl.bt <> Pass.BMethod then 
          log_and_skip (Error.make loc @@ Printf.sprintf "process %s : processes can't return non-void type" decl.name)
        else
          let* e = lower_rexp decl.generics e in
          let _,t as lt = e.info in 
          begin
          match decl.ret with 
          | None -> 
            log_and_skip (Error.make loc @@ Printf.sprintf "returns %s but %s doesn't return anything"  (string_of_sailtype (Some t)) decl.name)
          | Some r ->
            let+ _ = matchArgParam lt r decl.generics []  in
            buildStmt (Return (Some e))
          end

      | Block c ->
          ES.update (fun e -> THIREnv.new_frame e |> E.pure) >>
          let* res = aux c in 
          let+ () =  ES.update (fun e -> THIREnv.pop_frame e |> E.pure) in
          buildStmt (Block res)

      | Skip -> return (buildStmt Skip)
      | Watching (s, c) -> let+ res = aux c in buildStmt (Watching (s, res))
      | Emit s -> return (buildStmt (Emit s))
      | Await s -> return (buildStmt (When (s, buildStmt Skip)))
      | When (s, c) -> let+ res = aux c in buildStmt (When (s, res))
      | Run (id, el) ->
        let* el = ListM.map (lower_rexp decl.generics) el in
        (* let+ _ = check_call (snd id) el loc in *)
        buildStmt (Run (id, el)) |> return

      | Par (c1, c2) -> 
        let* env = ES.get in 
        let* c1 = aux c1 in
        ES.set env >>
        let+ c2 = aux c2 in
        buildStmt (Par (c1, c2))

      | DeclSignal s -> return (buildStmt (DeclSignal s))


    in 
    ES.run (aux decl.body env) |> Logger.recover (buildStmt dummy_pos Skip,snd env)

    let preprocess = Logger.pure
  end
)