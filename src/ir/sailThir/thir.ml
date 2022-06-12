
open Parser
open IrHir

(* translate_expression should have a typing environment parameter *)

module Pass : Common.Pass.StatementPass with 
              type in_body = AstParser.expression AstHir.statement and
              type out_body = AstThir.expression AstHir.statement = 
struct
  type in_body = AstParser.expression AstHir.statement
  type out_body = AstThir.expression AstHir.statement

  let _translate_expression (_e : AstParser.expression) : AstThir.expression = 
    failwith "TO DO"

  let translate _ = 
    AstHir.Skip Lexing.dummy_pos
end