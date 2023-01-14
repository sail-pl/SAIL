open SailParser
open Common
open TypesCommon
open Monad
open AstHir

type expression = loc AstHir.expression
type statement = expression AstHir.statement

open HirMonad.Make( struct
  type t = statement
  let mempty = Skip dummy_pos
  let mconcat = fun x y -> Seq (dummy_pos, x,y) 
  end)

module Pass = Pass.MakeFunctionPass (V)(
struct
  let name = "HIR"

  type in_body = AstParser.statement
  type out_body = statement
      

  let get_hint id env = 
    match List.nth_opt (HIREnv.get_closest env id) 0 with
    | None ->  ""
    | Some id ->  Printf.sprintf "Did you mean %s ?" id

  let lower_expression (e : AstParser.expression) : expression ECSW.t = 
    let open MonadSyntax(ECSW) in
    let open MonadFunctions(ECSW) in 

    let rec aux (e : AstParser.expression) : expression ECSW.t  = 
    match e with 
      | loc, Variable id  -> return (Variable (loc, id))
      | loc, Deref e -> 
        let+ e = aux e in Deref (loc, e)
      | loc, StructRead (e, id) ->
        let+ e = aux e in StructRead (loc, e, id)
      | loc, ArrayRead (e1, e2) ->
        let* e1 = aux e1 in 
        let+ e2 = aux e2 in 
        ArrayRead(loc,e1,e2)
      | loc , Literal l -> return (Literal (loc, l))
      | loc, UnOp (op, e) -> 
        let+ e = aux e in UnOp (loc, op, e)
      | loc, BinOp(op,e1,e2)->
        let* e1 = aux e1 in 
        let+ e2 = aux e2 in
        BinOp (loc, op, e1, e2)
      | loc, Ref (b, e) ->
        let+ e = aux e in Ref(loc, b, e)
      | loc, ArrayStatic el -> 
        let+ el = listMapM aux el in ArrayStatic (loc, el)
      | loc, StructAlloc (id, m) ->
        let+ m = mapMapM aux m in StructAlloc (loc, id, m)
      | loc, EnumAlloc (id, el) ->
        let+ el = listMapM aux el in  EnumAlloc (loc, id, el)
      | loc, MethodCall ((l_id,id), el) ->
          let* m = ECSW.get_method id in 
          match m with
          | Some (_proto_loc,proto) -> 
            begin
            match proto.ret with 
            | Some rtype -> 
              let* n = ECSW.fresh in 
              let x = "__f" ^ string_of_int n in
              let* el = listMapM aux el in
              let* () = DeclVar (dummy_pos, false, x, Some rtype, None) |> ECSW.write in
              let+ () = Invoke(loc, Some x, (l_id,id), el) |> ECSW.write in
              Variable (dummy_pos, x)
                
            | None -> ECSW.throw (Error.make loc "methods in expressions should return a value")
            end
          | _ -> let* env = ECSW.get_env in let hint = get_hint id env in ECSW.throw (Error.make l_id "unknown method" ~hint)
      in aux e

  let buildSeq s1 s2 = Seq (dummy_pos, s1, s2)

  let lower_function (c:in_body Pass.function_type) (env:HIREnv.t) : out_body E.t = 
    let open MonadSyntax(ECS) in
    let open MonadFunctions(ECSW) in 
    let open MonadOperator(ECS) in 
    
  let rec aux  : in_body -> out_body ECS.t   = function
    | l, DeclVar (mut, id, t, e ) -> 
      begin match e with 
        | Some e -> let+ (e, s) = lower_expression e in 
          buildSeq s (DeclVar (l, mut,id, t, Some e))
        | None -> return (DeclVar (l, mut,id, t, None))
      end 
    | l, Skip -> return (Skip l)
    | l, Assign(e1, e2) ->  
        let* e1,s1 = lower_expression e1 in
        let+ e2,s2 = lower_expression e2 in
        Seq (dummy_pos, s1, Seq (dummy_pos, s2, Assign(l, e1, e2)))
    

    | l, Seq (c1, c2) -> let+ c1 = aux c1 and* c2 = aux c2 in Seq(l, c1, c2) 
    | l, If (e, c1, Some c2) -> 
      let+ e,s = lower_expression e and* c1 = aux c1 and* c2 = aux c2 in 
      Seq (dummy_pos, s, If(l, e, c1, Some (c2)))

    | l, If ( e, c1, None) -> 
        let+ (e, s) = lower_expression e and* c1 = aux c1 in 
        Seq (dummy_pos, s, If(l, e, c1, None))
        
    | l, While (e, c) -> 
      let+ e,s = lower_expression e and* c = aux c in
      buildSeq s (While (l, e,c)) 
    | l, Loop c -> let+ c = aux c in While (l, Literal (dummy_pos, LBool true) , c) 

    | l, Break () -> return (Break l)
 (*   | Case(loc, e, cases) -> Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | l, Case (e, _cases) ->  let+ e,s = lower_expression e in
        buildSeq s (Case (l, e, []))

    | l, Invoke ((l_id,id) as lid, el) ->
        let* m = ECS.get_method id and* env = ECS.get in
        let* () = ECS.log_if (Option.is_none m) (let hint = get_hint id env in (Error.make l_id "unknown method" ~hint))
        in
        let+ el,s = listMapM lower_expression el in
        buildSeq s (Invoke (l, None, lid, el))

    | l, Return e -> 
        begin match e with 
        | None -> return (Return (l, None))
        | Some e -> let+ e,s = lower_expression e in
          buildSeq s (Return (l, Some e))
        end
    | l, Block c -> let+ c = aux c in Block (l, c) 
    
    | l, Run (l_id,id as lid, el) -> 
      let* () = ECS.log_if (id = c.name) (Error.make l_id "a process cannot call itself (yet)") in 
      let* m = ECS.get_process id and* env = ECS.get in
      let* () = ECS.log_if (Option.is_none m) (let hint = get_hint id env in (Error.make l_id "unknown process" ~hint)) in
      let* () =  ECS.log_if (c.bt = BMethod) (Error.make l_id "this is a process but methods cannot call processes") in
      let+ el,s = listMapM lower_expression el in buildSeq s (Run(l, lid, el))

    | l,_ when c.bt = Pass.BMethod -> 
      let+ () = ECS.log (Error.make l @@ Printf.sprintf "method %s : methods can't contain reactive statements" c.name) 
      in Skip(dummy_pos)

    | l, DeclSignal s -> return (DeclSignal (l,s))
    | l, Emit s -> return (Emit (l,s))
    | l, Await s -> return (When (l, s, Skip dummy_pos))
    | l, When (s, c) -> let+ c = aux c in When (l, s, c)
    | l, Watching (s, c) ->  let+ c = aux c in Watching (l, s, c)
    | l, Par (c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in Par(l, c1,c2)

    in
    ECS.run (aux c.body env) |> E.recover (Skip (dummy_pos))
  end
 )