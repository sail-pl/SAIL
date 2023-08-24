open Common
open Monad
open TypesCommon
open MonomorphizationUtils

type env = {monos: monomorphics; functions : sailor_functions; env: varTypesMap}

module MonoMonad = struct
  module S = MonadState.T(Error.Logger)(struct type t = env end)
  open MonadSyntax(S)
  open MonadOperator(S)
  include S
  (* error *)
  let throw e = E.throw e |> lift
  let throw_if e c = E.throw_if e c |> lift

  let get_decl id ty = get >>| fun e -> Env.get_decl id ty e.env
  let add_decl id decl ty = update (fun e -> E.bind (Env.add_decl id decl ty e.env) (fun env -> E.pure {e with env}))
  let get_var id = get >>| fun e -> Env.get_var id e.env
  let set_ve ve = update (fun e -> E.pure {e with env=(ve,snd e.env)})


  let add_fun mname (f: 'a sailor_method) = S.update (fun e -> E.pure {e with functions=FieldMap.add mname f e.functions})
  let get_funs = let+ e = S.get in e.functions

  let push_monos name generics = S.update (fun e -> E.pure {e with monos=(name,generics)::e.monos})
  let get_monos = let+ e = S.get in e.monos
  let pop_monos = let* e = S.get in 
    match e.monos with 
    | [] -> throw Error.(make dummy_pos "empty_monos") 
    | h::monos -> S.set {e with monos} >>| fun () -> h

  let run (decls:Env.D.t) (x: 'a t) : ('a * env) E.t = x {monos=[];functions=FieldMap.empty;env=Env.empty decls}

end


let mangle_method_name (name : string) (args : sailtype list) : string =
  let back =
    List.fold_left (fun s t -> s ^ string_of_sailtype (Some t) ^ "_") "" args
  in
  let front = "_" ^ name ^ "_" in
  let res = front ^ back in
  Logs.debug (fun m -> m "renamed %s to %s" name res);
  res