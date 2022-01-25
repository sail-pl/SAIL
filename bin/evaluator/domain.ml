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

open MonadOption
open MonadSyntax(MonadOption)

type tag = Field of string | Indice of int
type offset = tag list
type location = Heap.address * offset

module FieldMap = Map.Make (String)

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

type 'a result = Continue | Ret | Suspend of 'a

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
