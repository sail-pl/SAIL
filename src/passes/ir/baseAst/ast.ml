(**************************************************************************)
(*                                                                        *)
(*                                 SAIL                                   *)
(*                                                                        *)
(*             Frédéric Dabrowski, LMV, Orléans University                *)
(*                                                                        *)
(* Copyright (C) 2022 Frédéric Dabrowski                                  *)
(*                                                                        *)
(* This program is free software: you can redistribute it and/or modify   *)
(* it under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or      *)
(* (at your option) any later version.                                    *)
(*                                                                        *)
(* This program is distributed in the hope that it will be useful,        *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of         *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          *)
(* GNU General Public License for more details.                           *)
(*                                                                        *)
(* You should have received a copy of the GNU General Public License      *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>. *)
(**************************************************************************)

open Common.TypesCommon

type 'e struct_read = {field: l_str; strct: 'e}
type 'e struct_alloc = {name:l_str; fields: 'e locatable dict}
type 'e fcall = {ret_var : string option; id: l_str; args:'e list}

type yes = Yes
type no = No

type exp = Expression 
type stmt = Statement

(* based on https://icfp23.sigplan.org/details/ocaml-2023-papers/4/Modern-DSL-compiler-architecture-in-OCaml-our-experience-with-Catala *)

type ('tag,'kind,'features) generic_ast = ('tag, 'kind, 'features,'features) relaxed_ast
and ('tag,'kind, 'deep_features,'shallow_features) relaxed_ast = ('tag,('tag,'kind,'deep_features,'shallow_features) relaxed_ast_) tagged_node
and ('tag,'kind,'deep_features,'shallow_features) relaxed_ast_ =
  (* expressions *)
  | Variable :  string -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | Deref : ('tag,exp,'deep_features) generic_ast  -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | Ref : bool * ('tag,exp,'deep_features) generic_ast ->  ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | Literal : literal -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | UnOp : unOp * ('tag,exp,'deep_features) generic_ast -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | BinOp : {left: ('tag,exp,'deep_features) generic_ast; right:('tag,exp,'deep_features) generic_ast; op: binOp} -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | ArrayRead : {array: ('tag,exp,'deep_features) generic_ast ; idx: ('tag,exp,'deep_features) generic_ast} -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | ArrayStatic : ('tag,exp,'deep_features) generic_ast list -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_

  | MethodCall : (l_str option, ('tag,exp,'deep_features) generic_ast fcall) importable -> ('tag,exp,'deep_features,<methodCall:yes;..>) relaxed_ast_

  | StructRead : (l_str option, ('tag,exp,'deep_features) generic_ast struct_read) importable -> ('tag,exp,'deep_features, <resolvedImports:no;..>) relaxed_ast_

  | StructRead2 : (l_str, ('tag,exp,'deep_features) generic_ast struct_read) importable  -> ('tag,exp,'deep_features,<resolvedImports:yes;..>) relaxed_ast_

  | StructAlloc : (l_str option, ('tag,exp,'deep_features) generic_ast struct_alloc) importable -> ('tag,exp,'deep_features,<resolvedImports:no;..>) relaxed_ast_

  | StructAlloc2 : (l_str, ('tag,exp,'deep_features) generic_ast struct_alloc) importable -> ('tag,exp,'deep_features, <resolvedImports:yes;..>) relaxed_ast_

  | EnumAlloc : l_str * ('tag,exp,'deep_features) generic_ast list -> ('tag,exp,'deep_features,'shallow_features) relaxed_ast_
  
  (* statements *)

  | DeclVar : {mut:bool; id:string; ty: sailtype option; value: ('tag,exp,'deep_features) generic_ast option} -> ('tag,stmt,'deep_features, <typedDeclVar:no;..>) relaxed_ast_

  | DeclVar2 : {mut:bool; id:string; ty: sailtype} ->  ('tag,stmt,'deep_features, <typedDeclVar:yes;..> ) relaxed_ast_

  | Invoke : (l_str option, ('tag,exp,'deep_features) generic_ast fcall) importable -> ('tag,stmt, 'deep_features, <resolvedImports:no;..>) relaxed_ast_

  | Invoke2 : (l_str, ('tag,exp,'deep_features) generic_ast fcall) importable -> ('tag,stmt,'deep_features,<resolvedImports:yes;..>) relaxed_ast_

  | Skip : ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | Assign : {path: ('tag,exp,'deep_features) generic_ast ; value: ('tag,exp,'deep_features) generic_ast} -> ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | Seq : ('tag,stmt,'deep_features) generic_ast * ('tag,stmt,'deep_features) generic_ast ->  ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | If : 
    {
      cond: ('tag,exp,'deep_features) generic_ast; 
      then_:('tag,stmt,'deep_features) generic_ast ; 
      else_: ('tag,stmt,'deep_features) generic_ast option
    } ->  ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | Loop : ('tag,stmt,'deep_features) generic_ast ->  ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | Break :  ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | Case : {switch : ('tag,exp,'deep_features) generic_ast ; cases : (string * string list * ('tag, stmt, 'deep_features) generic_ast) list} ->  ('tag,stmt, 'deep_features, 'shallow_features) relaxed_ast_

  | Return : ('tag, exp,'deep_features) generic_ast option ->  ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_

  | Block : ('tag,stmt,'deep_features) generic_ast ->  ('tag,stmt,'deep_features,'shallow_features) relaxed_ast_




let buildExp (tag : 't) (node : ('t,exp,'a,'b) relaxed_ast_) : ('t,exp,'a,'b) relaxed_ast = {tag;node}
let buildStmt (tag : 't) (node : ('t,stmt,'a,'b) relaxed_ast_) : ('t,stmt,'a,'b) relaxed_ast = {tag;node}
let buildSeq tag s1 s2 = buildStmt tag (Seq (s1, s2))
let buildSeqStmt tag s1 s2 = buildSeq tag s1 @@ buildStmt tag s2


module Syntax = struct
    
  let skip : unit -> (loc,stmt,'a) generic_ast = fun () -> buildStmt dummy_pos Skip

  let (=) path value = buildStmt dummy_pos (Assign  {path;value})
  
  let var loc id ty value = buildStmt loc (DeclVar {mut=true;id;ty=Some ty;value})

  let true_ : unit -> (_,exp,_) generic_ast = fun () -> buildExp dummy_pos (Literal (LBool true))
  let false_ : unit -> (_,exp,_) generic_ast = fun () -> buildExp dummy_pos (Literal (LBool false))

  let (+) = fun left right -> buildExp dummy_pos (BinOp {op=Plus;left;right})
  let (%) = fun left right -> buildExp dummy_pos (BinOp {op=Rem;left;right})
  let (==) = fun left right -> buildExp dummy_pos (BinOp {op=Eq;left;right})

  let (&&) = fun s1 s2 -> buildStmt dummy_pos (Seq (s1,s2))
  let (!@) = fun id -> buildExp dummy_pos (Variable id)
  let (!) = fun n -> buildExp dummy_pos (Literal (LInt {l=Z.of_int n; size=32}))
  let (!!) = fun b -> buildStmt dummy_pos  (Block b)

  let if_ cond then_ else_ = 
    let else_ = match else_.node with Skip -> None | node ->  Some {else_ with node} in 
    buildStmt dummy_pos (If {cond;then_;else_}) 
end