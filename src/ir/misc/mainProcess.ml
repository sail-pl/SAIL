open Common
open SailModule
open TypesCommon

module E = Common.Error
open Monad.MonadSyntax(E.Logger)
open Monad.MonadOperator(E.Logger)


(* temporary pass, converts Main process into a method, throws error if not found or other processes exist *)
module Pass = Pass.Make( struct
  let name = "Main Process to Method"
  type in_body = IrMir.Mir.Pass.out_body
  type out_body  = in_body

  let add_return (m: in_body method_defn) : out_body method_defn = 
    let m_proto = {m.m_proto with rtype=Some (Int 32)} in
    let m_body = match m.m_body with
    | Right (decls,cfg) ->
      let b = IrMir.AstMir.BlockMap.find cfg.output cfg.blocks in
      (* hardcode "return 0" at the end *)
      let blocks = IrMir.AstMir.BlockMap.add cfg.output 
        {b with terminator=Some (Return (Some {info=(dummy_pos,Int 32); exp=(Literal (LInt {l=Z.zero;size=32}))}))} cfg.blocks in
      Either.right (decls,{cfg with blocks})
    | Left _ ->  m.m_body
    in
    {m_proto;m_body}

  let transform (m : in_body SailModule.t)  : out_body SailModule.t E.Logger.t =
  let+ main = method_of_process m "Main" <&> add_return in
  { m with methods = main :: m.methods} 
end
)