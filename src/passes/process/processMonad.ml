open Common
open TypesCommon
open IrHir

module V = (
  struct 
    type t = Read | Write
    let string_of_var = function Read -> "read" | Write -> "write"
    let param_to_var (_:param) = Read
  end
)


module M = struct
  open AstHir

  module E =  Error.Logger
  module Env = Env.VariableEnv(V)

  module SeqMonoid = struct

    type t = {decls : HirUtils.statement; init : HirUtils.statement ; loop : HirUtils.statement}

    let empty = {info=dummy_pos ; stmt=Skip}
    let concat s1 s2 = match s1.stmt,s2.stmt with
    | Skip, Skip -> empty
    | Skip,stmt | stmt,Skip -> {info=dummy_pos ; stmt}
    | _ -> {info=dummy_pos ; stmt=Seq (s1,s2)}
    let mempty = {decls=empty; init=empty ; loop=empty}
    let mconcat s1 s2 = {decls=concat s1.decls s2.decls; init = concat s1.init s2.init ; loop = concat s1.loop s2.loop}

  end

  module EC = MonadState.CounterTransformer(E)
  module ECW =  MonadWriter.MakeTransformer(EC)(SeqMonoid)
  module ECWS =  MonadState.T(ECW)(Env)
  include ECWS
  open Monad.UseMonad(ECWS)


  let throw_if_none b e = E.throw_if_none b e |> EC.lift |> ECW.lift |> lift

  let write_decls decls = ECW.write SeqMonoid.{decls; init=empty ; loop=empty} |> lift
  let write_init init = ECW.write SeqMonoid.{decls=empty; init; loop=empty} |> lift
  let write_loop loop = ECW.write SeqMonoid.{decls=empty; loop; init=empty} |> lift

  let declare_read_var loc id = ECWS.update (fun env -> Env.declare_var id (loc,Read) env |> EC.lift |> ECW.lift)
  let declare_write_var loc id = ECWS.update (fun env -> Env.declare_var id (loc,Write) env |> EC.lift |> ECW.lift)

  let throw_if b e = E.throw_if b e |> EC.lift |> ECW.lift |> lift 

  let fresh_prefix pname : string t = EC.fresh |> ECW.lift |> lift >>| fun i -> Fmt.str "%i%s" i pname


  let run : 'a t -> _ E.t = fun x -> E.bind (x Env.empty 0) (fun (((x,_e),body),_c) -> E.pure (x,body))
end