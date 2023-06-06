open Common
open TypesCommon

module E = Common.Error
open Monad.MonadSyntax(E.Logger)

(* temporary pass, converts Main process into a method, throws error if not found or other processes exist *)
module Pass = Pass.Make( 
struct
  let name = "Main Process to Method"
  type in_body = IrMir.Mir.Pass.out_body
  type out_body  = in_body

  let method_of_main_process (m: in_body SailModule.t) : out_body method_defn E.Logger.t = 
    let+ p = E.Logger.throw_if_none (List.find_opt (fun p -> p.p_name = "Main") m.processes)
                                    (E.make dummy_pos @@ "module '" ^ m.md.name ^ "' : no Main process found") 
    in
    let m_proto = {pos=p.p_pos; name="main"; generics = p.p_generics; params = fst p.p_interface; variadic=false; rtype=Some Int} in
    let m_body = 
      let decls,cfg = p.p_body in 
      let b = IrMir.AstMir.BlockMap.find cfg.output cfg.blocks in
      (* hardcode "return 0" at the end *)
      let blocks = IrMir.AstMir.BlockMap.add cfg.output 
        {b with terminator=Some (Return (Some {info=(dummy_pos,Int); exp=(Literal (LInt 0))}))} cfg.blocks in
      Either.right (decls,{cfg with blocks})
    in
    {m_proto; m_body}

  let transform (m : in_body SailModule.t)  : out_body SailModule.t E.Logger.t =
  let+ main = method_of_main_process m in
  { m with  methods = main :: m.methods } 
end
)