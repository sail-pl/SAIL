open Common
open TypesCommon
open Monad


module AstMonad(M : Monad) = struct
  open Ast
  open UseMonad(M)

  let opt_f f = function None -> return None | Some x -> let+ r = f x in Some r 


  type ('in_tag,'out_tag,'in_features,'out_features) map = {f: 'kind. ('in_tag,'kind,'in_features) Ast.generic_ast -> ('out_tag,'kind,'out_features) Ast.generic_ast M.t}


  let shallow_exp_map (type src_features dst_features in_tag out_tag)
  (map: (in_tag,exp,src_features) Ast.generic_ast -> (out_tag,exp,dst_features) Ast.generic_ast M.t) 
  (tag : out_tag)
  (x : (in_tag,exp,src_features,dst_features) Ast.relaxed_ast) 
  : (out_tag,exp,dst_features) Ast.generic_ast M.t = 
    let (node : (out_tag,exp,dst_features,dst_features) Ast.relaxed_ast_ M.t) = 
    match x.node with 
      | Variable id -> return @@ Variable id
      | Deref e -> let+ e = map e in Deref e
      | ArrayRead ar ->  let+ array = map ar.array and* idx = map ar.idx in ArrayRead {array;idx}
      | Literal l ->  return @@ Literal l
      | UnOp (op, e) -> let+ e = map e in UnOp (op, e)
      | BinOp bop -> let+ left = map bop.left and* right = map bop.right in BinOp {bop with left;right}
      | Ref (b, e) ->  let+ e = map e in Ref (b,e)
      | ArrayStatic el ->  let+ el = ListM.map map el in ArrayStatic el
      | EnumAlloc (id, el) ->  let+ el = ListM.map map el in EnumAlloc (id,el)
      | MethodCall mc -> let+ args = ListM.map map mc.value.args in  MethodCall {mc with value={mc.value with args}}
      | StructAlloc st ->  
        let+ fields = ListM.map (fun (s,(fi:_ locatable)) -> let+ value = map fi.value in s,{fi with value}) st.value.fields in 
        StructAlloc {st with value={st.value with fields}}
        
      | StructAlloc2 st -> 
        let+ fields = ListM.map (fun (s,(fi:_ locatable)) -> let+ value = map fi.value in s,{fi with value}) st.value.fields in 
        StructAlloc2 {st with value={st.value with fields}}

      | StructRead s ->  let+ strct = map s.value.strct in StructRead {s with value={s.value with strct} }
      | StructRead2 s ->  let+ strct = map s.value.strct in StructRead2 {s with value={s.value with strct} }
    in let+ node in {node;tag}
  

  let shallow_stmt_map (type src_features dst_features in_tag out_tag)
  (map_stmt: (in_tag,stmt,src_features) Ast.generic_ast -> (out_tag,stmt,dst_features) Ast.generic_ast M.t) 
  (map_exp: (in_tag,exp,src_features) Ast.generic_ast -> (out_tag,exp,dst_features) Ast.generic_ast M.t) 
  (tag : out_tag)
  (x : (in_tag,stmt,src_features,dst_features) Ast.relaxed_ast) 
  : (out_tag,stmt,dst_features) Ast.generic_ast M.t = 


    let (node : (out_tag,Ast.stmt,dst_features,dst_features) Ast.relaxed_ast_ M.t) = 
    match x.node with 
    | DeclVar v  -> let+ value = opt_f map_exp v.value in DeclVar {v with value}
    | DeclVar2 v  -> return (DeclVar2 v)
    | Assign a -> 
      let+ path = map_exp a.path
      and* value = map_exp a.value in 
      Assign {path;value}

    | Seq(c1, c2) -> 
      let+ c1 = map_stmt c1 
      and* c2 = map_stmt c2 in
      Seq (c1, c2)

    | If if_ -> 
      let+ cond = map_exp if_.cond
      and* then_ = map_stmt if_.then_ 
      and* else_  = opt_f map_stmt if_.else_ in
      If {cond;then_;else_}

    | Loop c -> let+ c = map_stmt c in Loop c
    | Break -> return Break
    | Case c -> 
      let+ switch = map_exp c.switch 
      and* cases = ListM.map (fun (s,s2,s3) -> let+ s3 = map_stmt s3 in s,s2,s3) c.cases in 
      Case {switch;cases}

    | Invoke i -> 
      let+ args = ListM.map map_exp i.value.args in
      Invoke {i with value = {i.value with args}}

    | Invoke2 i ->  
      let+ args = ListM.map map_exp i.value.args in
      Invoke2 {i with value = {i.value with args}}

    | Return e -> let+ e = opt_f map_exp e in Return e
    | Block c -> let+ c = map_stmt c in Block c
    | Skip -> return Skip  
    in let+ node in {node;tag}


    let separate_kind (type src_features dst_features in_tag out_tag kind) 
    (f_stmt :  (in_tag,stmt,src_features,dst_features) Ast.relaxed_ast -> (out_tag,stmt,dst_features) Ast.generic_ast M.t)  
    (f_exp :  (in_tag,exp,src_features,dst_features) Ast.relaxed_ast -> (out_tag,exp,dst_features) Ast.generic_ast M.t) 
    (x: (in_tag,kind,src_features,dst_features) Ast.relaxed_ast) : (out_tag, kind, dst_features) generic_ast M.t = 
  
    let f_stmt : (in_tag, stmt,src_features,dst_features) relaxed_ast_ -> (out_tag, stmt, dst_features) generic_ast M.t = fun node -> f_stmt {node;tag=x.tag} in
    let f_exp : (in_tag,exp,src_features,dst_features) relaxed_ast_ -> (out_tag, exp, dst_features) generic_ast M.t = fun node -> f_exp {node;tag=x.tag} in
  
    match (x.node : (in_tag,kind,src_features,dst_features) Ast.relaxed_ast_) with
    | StructAlloc _ as exp -> f_exp exp
    | StructAlloc2 _ as exp -> f_exp exp
    | StructRead _  as exp -> f_exp exp
    | StructRead2 _  as exp -> f_exp exp
    | MethodCall _ as exp -> f_exp exp
    | Variable _ as exp -> f_exp exp
    | Deref _ as exp -> f_exp exp
    | ArrayRead _ as exp -> f_exp exp
    | Literal _ as exp -> f_exp exp
    | UnOp _ as exp -> f_exp exp
    | BinOp _ as exp -> f_exp exp
    | Ref _ as exp -> f_exp exp
    | ArrayStatic _ as exp -> f_exp exp
    | EnumAlloc _ as exp -> f_exp exp
    | DeclVar _ as stmt -> f_stmt stmt
    | DeclVar2 _ as stmt -> f_stmt stmt
    | Assign _ as stmt -> f_stmt stmt
    | Seq _ as stmt -> f_stmt stmt
    | If _ as stmt -> f_stmt stmt
    | Loop _ as stmt -> f_stmt stmt
    | Break as stmt -> f_stmt stmt
    | Case _ as stmt -> f_stmt stmt
    | Invoke _ as stmt -> f_stmt stmt
    | Invoke2 _ as stmt -> f_stmt stmt
    | Return _ as stmt -> f_stmt stmt
    | Block _ as stmt -> f_stmt stmt
    | Skip as stmt -> f_stmt stmt

  let shallow_map (type src_features dst_features in_tag out_tag kind)
                  (map: (in_tag,out_tag,src_features,dst_features) map) 
                  (tag : out_tag) 
                  (x : (in_tag,kind,src_features,dst_features) Ast.relaxed_ast) 
                  : (out_tag,kind,dst_features) Ast.generic_ast M.t = 
    separate_kind (shallow_stmt_map map.f map.f tag) (shallow_exp_map map.f tag) x

end

let rename_var  (f: string -> string) x   = 
  let module Map = AstMonad(MonadIdentity) in 
  let open Ast in 
  let rec aux :  type kind features tag. (tag,kind,features) generic_ast -> (tag,kind,features) generic_ast = fun x ->
    let ret  :  (_,kind,features,features) relaxed_ast_ -> (_,kind,features) generic_ast = fun n -> mk_tagged_node x.tag n in 
    match x.node with 
    | Variable id -> ret @@ Variable (f id)
    | DeclVar v  -> 
      let value = MonadOption.M.fmap aux v.value in
      let id = f v.id in 
      ret @@ DeclVar {v with value; id}
    | Invoke i -> 
      let args = List.map aux i.value.args in 
      let ret_var = MonadOption.M.fmap f i.value.ret_var in
      ret @@ Invoke {i with value = {i.value with ret_var;args}}
    | _ as x' -> Map.shallow_map {f=aux} x.tag {tag=x.tag;node=x'} 
    in aux x
