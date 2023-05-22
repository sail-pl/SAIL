open Common

module E = Common.Error
open Monad.MonadSyntax(E.Logger)


module Pass = Pass.Make( 
struct
  let name = "Monomorphization (todo)"
  type in_body = IrMir.Mir.Pass.out_body
  type out_body  = in_body


  let transform (smdl : in_body SailModule.t)  : out_body SailModule.t E.Logger.t =
  (* todo *)
  return smdl
end
)
