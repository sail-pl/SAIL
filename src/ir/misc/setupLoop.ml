open Common
open TypesCommon

module E = Common.Error
open Monad.MonadSyntax(E.Logger)

module Pass = Pass.Make( struct
let name = "Setup / Loop for embedded devices"
type in_body = IrHir.Hir.Pass.out_body
type out_body  = in_body

open IrHir.AstHir
 let bs = buildStmt dummy_pos

  let createMainProcess (m: in_body SailModule.t) : out_body process_defn Error.Logger.t = 
    let* setup = E.Logger.throw_if_none 
                (E.make dummy_pos @@ "module '" ^ m.md.name ^ "' : no 'setup' function found" )
                (List.find_opt (fun m -> m.m_proto.name = "setup") m.methods) 

    in 
    let+ () = E.Logger.throw_if 
      (E.make setup.m_proto.pos "'setup' procedure doesn't take any parameter")
      (setup.m_proto.params <> []) 

    and* () = E.Logger.throw_if
      (E.make setup.m_proto.pos "'setup' function is a procedure")
      (Option.is_some setup.m_proto.rtype) 

    
    in
    let call_setup = Invoke (None,None,(dummy_pos,"setup"),[]) in
    let call_loop = Invoke (None,None,(dummy_pos,"loop"),[]) in
    let whle = Loop (bs call_loop) in

    let stmt = Seq (bs call_setup, bs whle)
    in
    {
      p_pos = dummy_pos;
      p_name = "Main";
      p_generics = [];
      p_interface = [],[];
      p_body= {info=dummy_pos; stmt};
    }


  let transform (m : in_body SailModule.t)  : out_body SailModule.t E.Logger.t =
    let open SailModule in 
    let* loop = method_of_process m "Loop" in
    let loop_decl = method_decl_of_defn loop in
    let* declEnv = DeclEnv.add_decl loop.m_proto.name loop_decl Method m.declEnv in
    let+ main = createMainProcess m in
    { m with methods = loop::m.methods ; processes = main :: m.processes ; declEnv} 
  end
)
