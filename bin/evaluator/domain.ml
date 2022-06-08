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
open Common
open Intermediate

open MonadOption
open MonadSyntax(MonadOption)


type tag = Field of string | Indice of int

type offset = tag list

type kind = Owned | Borrowed of offset * bool

type location = Heap.address * kind

(** kind : wether the location is owned or (mutually) borrowed *)
type value =
  | VBool of bool
  | VInt of int
  | VFloat of float
  | VChar of char
  | VString of string
  | VStruct of string * value FieldMap.t
  | VEnum of string * value list
  | VLoc of location
  | Moved 

let valueOfLiteral c =
  match c with
  | LBool x -> VBool x
  | LInt x -> VInt x
  | LFloat x -> VFloat x
  | LChar x -> VChar x
  | LString x -> VString x

let rec readValue (v : value) (o : offset) : value option =
  match (v, o) with
  | _, [] -> Some v
  | VStruct (_, m), Field f :: o' -> 
      let* v = FieldMap.find_opt f m in readValue v o'
  | _ -> None

let rec updateValue (v : value) (o : offset) (w : value) : value option =
  match (v, o) with
  | _, [] -> Some w
  | VStruct (id,m), Field f :: o' ->
      let* vf = FieldMap.find_opt f m in
        let* v' = updateValue vf o' w in
        Some (VStruct (id,FieldMap.update f (fun _ -> Some v') m))
  | _ -> None
  
type frame = Heap.address Env.frame

type env = Heap.address Env.t

type heap = (value, bool) Either.t Heap.t

type 'a status = Continue | Ret | Suspend of 'a

(* A command is a statement decorated with frames *)

type command =
  | DeclVar of bool * string * sailtype * expression option
  | DeclSignal of string
  | Skip
  | Assign of path * expression
  | Seq of command * command
  | Block of command * frame
  | If of expression * command * command
  | While of expression * command
  | Case of expression * (pattern * command) list
  | Invoke of string * expression list
  | Return
  | Emit of string
  | When of string * command * frame
  | Watching of string * command * frame
  | Par of command * frame * command * frame

  let rec initCommand (c : statement) : command = 
    match c with 
    | Intermediate.DeclVar (b,x,t,e) -> DeclVar(b,x,t,e)
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
  | UnMutableLocation of Heap.address
  | CantDropNotOwned of Heap.address
  | Division_by_zero
  | MovedPointer of Heap.address
  | NonLinearPointer
  | InvalidSignal 

module Result = ErrorMonadEither.Make(struct type t = error end)


let mapM (f : 'a -> 'b Result.t) (s : 'a FieldMap.t) : 'b FieldMap.t Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  let rec aux (l : (string * 'a) Seq.t) : (string * 'b) Seq.t Result.t =
    match l () with
    | Seq.Nil -> return (fun () -> Seq.Nil)
    | Seq.Cons ((x, a), v) -> (
        match (f a, aux v) with
        | Either.Left u, _ -> throwError u
        | Either.Right u, Either.Right l' ->
            return (fun () -> Seq.Cons ((x, u), l'))
        | Either.Right _, Either.Left l' -> throwError l')
  in
  match aux (FieldMap.to_seq s) with
  | Either.Right s -> Either.Right (FieldMap.of_seq s)
  | Either.Left e -> Either.Left e

  let foldM (f : 'a -> (string * 'b) -> 'a Result.t) (x :'a) (y : 'b FieldMap.t) : 'a Result.t =  
    let open Result in
    let open MonadSyntax (Result) in
    let rec aux (l : (string * 'b) Seq.t) : 'a Result.t =
        match l () with 
            Seq.Nil -> return x
        |   Seq.Cons ((y, a), v) -> (
                match aux v with 
                    Either.Left u -> throwError u
                |   Either.Right u ->  f u (y, a)
        )
    in match aux (FieldMap.to_seq y) with 
    | Either.Right s -> Either.Right s
    | Either.Left e -> Either.Left e 
