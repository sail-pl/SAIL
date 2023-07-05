open Common
open TypesCommon
open IrHir

module M = struct
  open AstHir


  module E =  Error.Logger

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
  include ECW
  open Monad.UseMonad(ECW)


  let throw_if_none b e = E.throw_if_none b e |> EC.lift |> lift

  let write_decls decls = ECW.write SeqMonoid.{decls; init=empty ; loop=empty}
  let write_init init = ECW.write SeqMonoid.{decls=empty; init; loop=empty}
  let write_loop loop = ECW.write SeqMonoid.{decls=empty; loop; init=empty}

  let throw_if b e = E.throw_if b e |> EC.lift |> lift 

  let fresh_prefix pname = EC.fresh |> lift >>| fun i -> Fmt.str "%i%s_" i pname


  let run : 'a t -> ('a * 'b) E.t = fun x -> E.bind (x 0) (fun (x,_c) -> E.pure x)
end