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

open Saillib.Env
open Saillib.Heap
open Saillib.Monad
open Saillib.Option
open Saillib.Error
open Intermediate
open Common

open MonadOption
open MonadSyntax(MonadOption)

type tag = Field of string | Indice of int
type offset = tag list
type location = Heap.address * offset

type value =
  | VBool of bool
  | VInt of int
  | VFloat of float
  | VChar of char
  | VString of string
  | VArray of value list
  | VStruct of value FieldMap.t
  | VEnum of string * value list
  | VLoc of location

type frame = Heap.address Env.frame
type env = Heap.address Env.t
type heap = (value, bool) Either.t Heap.t

type 'a status = Continue | Ret | Suspend of 'a

(* type expression =
  | Var of string
  | Literal of Common.literal
  | UnOp of Common.unOp * expression
  | BinOp of Common.binOp * expression * expression
  | ArrayAlloc of expression list
  | ArrayRead of expression * expression
  | StructAlloc of expression FieldMap.t
  | StructRead of expression * string
  | EnumAlloc of string * expression list
  | Ref of bool * expression
  | Deref of expression *)

type command =
  | DeclVar of bool * string * Common.sailtype 
  | DeclSignal of string
  | Skip
  | Assign of expression * expression
  | Seq of command * command
  | Block of command * frame
  | If of expression * command * command
  | While of expression * command
  | Case of expression * (Common.pattern * command) list
  | Invoke of string * expression list
  | Return
  | Emit of string
  | When of string * command * frame
  | Watching of string * command * frame
  | Par of command * frame * command * frame

  let rec initCommand (c : Intermediate.command) : command = 
    match c with 
    | Intermediate.DeclVar (b,x,t) -> DeclVar(b,x,t)
     | Intermediate.DeclSignal (s) -> DeclSignal(s)
    | Intermediate.Skip -> Skip
    | Intermediate.Assign(e1, e2) -> Assign(e1, e2)
    | Intermediate.Seq (c1, c2) -> Seq(initCommand c1, initCommand c2)
    | Intermediate.Block(c) -> Block (initCommand c, Env.emptyFrame)
    | Intermediate.If (e,c1,c2) -> If(e, initCommand c1, initCommand c2)
    | Intermediate.While (e,c) -> While (e, initCommand c)
    | Intermediate.Case (e, pl) -> Case(e, List.map (fun (p, c) -> (p, initCommand c)) pl)
    | Intermediate.Invoke (x,el) -> Invoke(x,el)
    | Intermediate.Return -> Return
    | Intermediate.Emit (s) -> Emit(s)
    | Intermediate.When(s,c) -> When(s, initCommand c, Env.emptyFrame)
    | Intermediate.Watching(s,c) -> Watching(s, initCommand c, Env.emptyFrame)
    | Intermediate.Par (c1, c2) -> Par (initCommand c1, Env.emptyFrame, initCommand c2, Env.emptyFrame) 

type error = 
  | TypingError 
  | UnknownMethod of string
  | UnknownVariable of string
  | UnknownField of string 
  | UnknownSignal of string
  | UndefinedOffset of value * offset
  | UnitializedAddress of Heap.address
  | UndefinedAddress of Heap.address
  | OutOfBounds of int
  | IncompletePatternMatching of value
  | MissingReturnStatement
  | ReturnStatementInProcess
  | NotASignalState
  | InvalidStack
  | NotALeftValue
  | NotAValue
  | Division_by_zero

module Result = ErrorMonadEither.Make(struct type t = error end)

let locationOfAddress (a : Heap.address) : location = (a, [])

let rec readValue (v : value) (o : offset) : value option =
  match (v, o) with
  | _, [] -> Some v
  | VStruct m, Field f :: o' -> FieldMap.find_opt f m >>= (Fun.flip readValue) o'
  | VArray a, Indice n :: o' -> List.nth_opt a n >>= (Fun.flip readValue) o'
  | _ -> None

let rec updateValue (v : value) (o : offset) (w : value) : value option =
  match (v, o) with
  | _, [] -> Some w
  | VStruct m, Field f :: o' ->
      let* vf = FieldMap.find_opt f m in
      let* v' = updateValue vf o' w in
      Some (VStruct (FieldMap.update f (fun _ -> Some v') m))
  | VArray a, Indice n :: o' ->
      let* vn = List.nth_opt a n in
      let* v' = updateValue vn o' w in
      Some (VArray (List.mapi (fun i x -> if i = n then v' else x) a))
  | _ -> None
