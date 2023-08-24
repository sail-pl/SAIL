open Common
open TypesCommon
open ProcessMonad
open Monad.UseMonad(M)
open IrHir
module E = Error.Logger
module D = SailModule.Declarations

type body = (Hir.statement,(Hir.statement,Hir.expression) SailParser.AstParser.process_body) SailModule.methods_processes

let method_of_main_process (p : 'a process_defn): 'a method_defn = 
  let m_proto = {pos=p.p_pos; name="main"; generics = p.p_generics; params = p.p_interface.p_params; variadic=false; rtype=None; extern=false} 
  and m_body = Either.right p.p_body in
  {m_proto;m_body}


let finalize (proc_def,(new_body: M.ECW.elt)) = 
  let open AstHir in
  let (++) = M.SeqMonoid.concat in 

  let main = method_of_main_process proc_def in 
  let m_body = 
    new_body.decls ++ 
    new_body.init ++
    buildStmt dummy_pos (Loop new_body.loop )
    |> Either.right  
  in {main with m_body}


type 'a proc_tree = P of 'a process_defn * 'a proc_tree list

let ppPrintModule (pf : Format.formatter) (m : body SailModule.t ) : unit = 
  let open Format in 
  fprintf pf "// Sail HIR Representation: %s\n%a" m.md.name 
  (pp_print_list Pp_hir.ppPrintMethod) m.body.methods
  (* (pp_print_list ~pp_sep:pp_comma ppPrintProcess) m.body.processes *)


let find_process_source (name: l_str) (import : l_str option) procs : 'a process_defn option M.t =
  let* _,env = M.get in 
  let* (_,origin),_ = HirUtils.find_symbol_source ~filt:[P()] name import env |> M.from_error in
  let+ procs = 
    if origin = HirUtils.D.get_name env then return procs
    else
      let find_import = List.find_opt (fun i -> i.mname = origin) (HirUtils.D.get_imports env) in
      let+ i = M.throw_if_none Error.(make dummy_pos "can't happen") find_import in 
      let sm = In_channel.with_open_bin (i.dir ^ i.mname ^ Constants.mir_file_ext) @@ fun c -> (Marshal.from_channel c : Mono.MonomorphizationUtils.out_body SailModule.t)
      in sm.body.processes
  in
  List.find_opt (fun (p:_ process_defn) -> p.p_name = snd name) procs
