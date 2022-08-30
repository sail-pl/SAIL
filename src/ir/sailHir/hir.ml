open SailParser
open Common
open TypesCommon
open Monad
open Monoid
open Error
open AstHir

type expression = loc AstHir.expression
type statement = expression AstHir.statement

module MonoidSeq: Monoid with type t = statement = struct
  type t = statement
  let mempty = Skip dummy_pos
  let mconcat = fun x y -> Seq (dummy_pos, x,y) 
end 


module V : Env.Variable = struct 
type t = unit
let string_of_var _ = ""
let to_var _ _ _ = ()
end

module HIREnv = SailModule.SailEnv(V)
  
module W = MonadWriter.Make (MonoidSeq)
module R = MonadReader.M(HIREnv)
module C = MonadState.Counter
module E = MonadError
module EC = MonadState.CounterTransformer(E)
module ECR =  MonadReader.T(EC)(HIREnv)
module ECRW = MonadWriter.MakeTransformer(ECR)(MonoidSeq)


module Pass = Pass.MakeFunctionPass (V)(
struct
  type in_body = AstParser.statement
  type out_body = statement
      

  let lower_expression (e : AstParser.expression) : expression ECRW.t = 
    let open MonadSyntax(ECRW) in
    let open MonadFunctions(ECRW) in 

    let rec aux (e : AstParser.expression) : expression ECRW.t  = 
    match e with 
      | loc, Variable id  -> return (Variable(loc, id))
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
      | loc, MethodCall (id, el) ->
        let open MonadSyntax(R) in 
          let* env = R.read  in 
          match HIREnv.get_method env id with
          | Some (_proto_loc,proto) -> 
            begin
            match proto.ret with 
            | Some rtype -> 
              let open MonadSyntax(ECR) in 
              let* n = EC.fresh |> R.pure in 
              let x = "__f" ^ string_of_int n in
              let+ el,_ = listMapM aux el in
              let open MonadSyntax(W) in 
              let* () = DeclVar (dummy_pos, false, x, Some rtype, None) |> W.write in
              let+ () = Invoke(loc, Some x, id, el) |> W.write in
              Variable (dummy_pos, x)
                
            | None ->  Result.error [loc,"error methods in expressions should return a value"] |> EC.lift |> ECR.lift
            end
          | _ -> Result.error [loc, "call to undefined method"] |> EC.lift |> ECR.lift
      in aux e

  let buildSeq s1 s2 = Seq (dummy_pos, s1, s2)

  let lower_function (c:in_body Pass.function_type) (env:HIREnv.t) : out_body E.t = 
    let open MonadSyntax(ECR) in
    let open MonadFunctions(ECRW) in 
    let open MonadOperator(E) in 
  let rec aux  : in_body -> out_body ECR.t   = function
    | l, DeclVar (mut, id, t, e ) -> 
      begin match e with 
        | Some e -> let+ (e, s) = lower_expression e in 
          buildSeq s (DeclVar (l, mut,id, t, Some e))
        | None -> DeclVar (l, mut,id, t, None) |> ECR.pure
      end 

    | l, DeclSignal s -> DeclSignal (l,s) |> ECR.pure
    | l, Skip -> Skip(l) |> ECR.pure
    | l, Assign(e1, e2) ->  
        let* e1,s1 = lower_expression e1 in
        let+ e2,s2 = lower_expression e2 in
        Seq (dummy_pos, s1, Seq (dummy_pos, s2, Assign(l, e1, e2)))
    

    | l, Seq(c1, c2) -> let+ c1 = aux c1 and* c2 = aux c2 in Seq(l, c1, c2) 
    | l, Par(c1, c2) ->  let+ c1 = aux c1 and* c2 = aux c2 in Par(l, c1,c2)
    | l, If(e, c1, Some c2) -> 
      let+ e,s = lower_expression e and* c1 = aux c1 and* c2 = aux c2 in 
      Seq (dummy_pos, s, If(l, e, c1, Some (c2)))

    | l, If( e, c1, None) -> 
        let+ (e, s) = lower_expression e and* c1 = aux c1 in 
        Seq (dummy_pos, s, If(l, e, c1, None))
        
    | l, While(e, c) -> 
      let+ (e, s) = lower_expression e and* c = aux c in
      buildSeq s (While(l, e,c))

 (*   | Case(loc, e, cases) -> Case (loc, e, List.map (fun (p,c) -> (p, aux c)) cases) *)
    | l, Case(e, _cases) ->  let+ e,s = lower_expression e in
        buildSeq s (Case (l, e, []))

    | l, Invoke(id, el) -> fun e -> 
        let open MonadSyntax(EC) in
        let+ (el,s) = listMapM lower_expression el e in
        buildSeq s (Invoke(l, None, id, el))
      
    | l, Return e -> 
        begin match e with 
        | None -> Return(l, None) |> ECR.pure 
        | Some e -> let+ e,s = lower_expression e in
          buildSeq s (Return(l, Some e))
      end

    | l, Run(id, el) -> let+ el,s = listMapM lower_expression el in buildSeq s (Run(l, id, el))
    | l, Loop c -> let+ c = aux c in While(l, Literal(dummy_pos, LBool true) , c) 
    | l, Emit s -> Emit(l,s) |> ECR.pure
    | l, Await s -> When(l, s, Skip(dummy_pos)) |> ECR.pure
    | l, When (s, c) -> let+ c = aux c in When(l, s, c)
    | l, Watching(s, c) ->  let+ c = aux c in Watching(l, s, c)
    | l, Block c -> let+ c = aux c in Block(l, c) 
      
    in
    Logs.debug (fun m -> m "lowering to HIR %s" c.name); 
    EC.run (aux c.body env)
  end
 )