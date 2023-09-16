open Common
open TypesCommon
open IrThir
open IrMir
open IrHir
open SailParser

module E = Common.Logging.Logger
module Env = SailModule.DeclEnv
open Monad.UseMonad(E)

let read_imports (imports : ImportSet.t) : (string * Mir.Pass.out_body SailModule.t) list  = 
List.map (fun i ->  
  Logs.debug (fun m -> m "reading mir for import '%s' (%s)" i.mname i.dir); 
  i.dir,In_channel.with_open_bin (i.dir ^ i.mname ^ Constants.mir_file_ext) @@ fun c -> (Marshal.from_channel c : Mir.Pass.out_body SailModule.t)
) (ImportSet.elements imports)

module Pass = Pass.Make( struct
  let name = "Get imported modules imports"
  type in_body = (ThirUtils.statement,(HirUtils.statement,HirUtils.expression) AstParser.process_body) SailModule.methods_processes
  type out_body  = in_body

  let set_fcall_source (m:in_body SailModule.t) : out_body SailModule.t E.t = 
    let imports = read_imports m.imports in

    let+ libs,methods = 
      ListM.fold_left_map (fun libs f -> 
      match f.m_body with
      | Right _ -> 
        (libs,f) |> E.pure
      | Left (realname,lib) -> (* extern method, give it its realname for codegen *)
        let m_proto = {f.m_proto with name=realname} in
        let libs = FieldSet.add_seq (List.to_seq lib) libs in
        return (libs,{f with m_proto}) (* add lib required by ffi *)
      ) FieldSet.empty m.body.methods 
    in
    (* the imports of my imports are my imports and same goes for the libs *)
    let libs,imports =  List.fold_left (
      fun (libs,imports) (_,(i:'a SailModule.t)) -> 
        FieldSet.union libs i.md.libs , ImportSet.union i.imports imports
      ) (libs,ImportSet.empty) imports in

      (* we add our imports last *)
      (* 
        fixme : the way this works is not correct : it relies on recompiling every dependencies and giving them an order based on how deep the imports are from the original module
        if an other module requires the same dependency and does not recompile them, the compilation order from the previous one will still be there...
      *)

      let imports = ImportSet.(diff m.imports imports  |> union imports ) in 
    
    {m with body = SailModule.{methods ; processes=m.body.processes}; imports; md={m.md with libs}}



  let add_imports (smdl : out_body SailModule.t) : out_body SailModule.t = 
    let sorted_imports = (smdl.imports |> ImportSet.diff smdl.imports |> ImportSet.elements |> List.sort (fun i1 i2 -> Int.compare i1.proc_order i2.proc_order)) in 
    let declEnv = 
      List.fold_left (fun (e:Env.t) (i:import)  -> 
        Logs.debug (fun m -> m "processing import %s" i.mname);
        let sm = In_channel.with_open_bin (i.dir ^ i.mname ^ Constants.mir_file_ext) @@ fun c -> (Marshal.from_channel c : 'a SailModule.t)
        in
        Env.add_import_decls (i,sm.declEnv) e 
      ) smdl.declEnv sorted_imports
    in
    {smdl with declEnv}
  



  let transform (smdl : in_body SailModule.t)  : out_body SailModule.t E.t =
    Logs.debug (fun m -> m "imports : %s" (String.concat " " (List.map (fun i -> i.mname) (ImportSet.elements smdl.imports))));
    set_fcall_source smdl >>| add_imports
end
)