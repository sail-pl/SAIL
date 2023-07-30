open Common
open TypesCommon
open ProcessMonad
open Monad.UseMonad(M)
open IrHir
module E = Error.Logger

type body = (Hir.statement,(Hir.statement,Hir.expression) SailParser.AstParser.process_body) SailModule.methods_processes

let method_of_main_process (p : 'a process_defn): 'a method_defn = 
  let m_proto = {pos=p.p_pos; name="main"; generics = p.p_generics; params = fst p.p_interface; variadic=false; rtype=None; extern=false} 
  and m_body = Either.right p.p_body in
  {m_proto;m_body}



let prefix_exp prefix (e: _ AstHir.expression) = 
  let open AstHir in 
  let rec aux (e : _ expression) = 
    let buildExp = buildExp e.info in 
    match e.exp with 
    | Variable id -> buildExp @@ Variable (prefix ^ id)
    | Deref e -> let e = aux e in buildExp @@ Deref e
    | StructRead (mod_loc,e, id) -> let e = aux e in buildExp @@ StructRead(mod_loc,e,id)
    | ArrayRead (e1, e2) ->
      let e1 = aux e1 in 
      let e2 = aux e2 in 
      buildExp @@ ArrayRead (e1,e2)
    | Literal _ as l -> buildExp l
    | UnOp (op, e) -> let e = aux e in buildExp @@ UnOp (op,e)
    | BinOp(op,e1,e2)->
      let e1 = aux e1 in 
      let e2 = aux e2 in
      buildExp @@ BinOp(op,e1,e2)
    | Ref (b, e) ->
      let e = aux e in buildExp @@ Ref(b,e)
    | ArrayStatic el -> let el = List.map aux el in buildExp @@ ArrayStatic el
    | StructAlloc (origin,id, m) -> let m = List.map (fun (n,e) -> n,aux e) m in buildExp @@ StructAlloc (origin,id,m)
    | EnumAlloc (id, el) -> let el = List.map aux el in buildExp @@ EnumAlloc (id,el)
    | MethodCall (mod_loc, id, el) -> let el  = List.map aux el in buildExp @@ MethodCall (mod_loc,id,el)
    in aux e

let prefix_stmt prefix s = 
  let open AstHir in 
  let prefix_exp = prefix_exp prefix in 
  let rec aux (s : _ statement) = 
    let buildStmt = buildStmt s.info in
    match s.stmt with
    | DeclVar (mut, id, opt_t,opt_exp) -> 
      let e = Option.(bind opt_exp (fun e -> prefix_exp e |> some)) in
      buildStmt @@ DeclVar (mut,prefix ^ id,opt_t,e)
    | Assign(e1, e2) -> 
      let e1 = prefix_exp e1
      and e2 = prefix_exp e2 in 
      buildStmt @@ Assign(e1, e2)
    | Seq(c1, c2) -> 
      let c1 = aux c1 in
      let c2 = aux c2 in
      buildStmt  @@ Seq(c1, c2)
    | If(cond_exp, then_s, else_s) -> 
      let cond_exp = prefix_exp cond_exp in
      let then_s = aux then_s in
      let else_s  = Option.(bind else_s (fun s -> aux s |> some)) in
      buildStmt (If(cond_exp, then_s, else_s))
    | Loop c -> let c = aux c in buildStmt (Loop c)
    | Break -> buildStmt Break
    | Case(e, _cases) -> let e = prefix_exp e in buildStmt (Case (e, []))
    | Invoke (var, mod_loc, id, el) -> 
      let el = List.map prefix_exp el in 
      let var = Option.(bind var (fun v -> prefix ^ v |> some)) in
      buildStmt @@ Invoke(var,mod_loc, id,el)
    | Return e -> let e = Option.(bind e (fun e -> prefix_exp e |> some)) in buildStmt @@ Return e
    | Block c -> let c = aux c in buildStmt (Block c)
    | Skip -> buildStmt Skip
    in
    aux s

let finalize (proc_def,(new_body: M.elt)) = 
  let open AstHir in
  let (++) = M.SeqMonoid.concat in 

  let main = method_of_main_process proc_def in 
  let m_body = 
    new_body.decls ++ 
    new_body.init ++
    buildStmt dummy_pos (Loop new_body.loop )
    |> Either.right  
  in {main with m_body}


type 'a proc_tree = P of 'a process_defn * 'a proc_tree list

let ppPrintModule (pf : Format.formatter) (m : body SailModule.t ) : unit = 
  let open Format in 
  fprintf pf "// Sail HIR Representation: %s\n%a" m.md.name 
  (pp_print_list Pp_hir.ppPrintMethod) m.body.methods
  (* (pp_print_list ~pp_sep:pp_comma ppPrintProcess) m.body.processes *)