open Domain
open Saillib.Monad
open Saillib.Env
open Saillib.Heap
open Common

let resultOfOption (e : error) (f : 'a -> 'b option) (x : 'a) : 'b Result.t =
  let open Result in
  let open MonadSyntax (Result) in
  match f x with None -> throwError e | Some y -> return y

let getVariable env x =
  resultOfOption (UnknownVariable x) (Env.getVariable env) x

let getLocation h a = resultOfOption (UndefinedAddress a) (Heap.getLocation h) a

let setLocation h (a, v) =
  resultOfOption (UndefinedAddress a) (Heap.update h) (a, v)

let getField m f = resultOfOption (UnknownField f) (FieldMap.find_opt f) m
let getIndex a n = resultOfOption (OutOfBounds n) (List.nth_opt a) n
let getOffset v o = resultOfOption (UndefinedOffset (v, o)) (readValue v) o

let setOffset v o v' =
  resultOfOption (UndefinedOffset (v, o)) (updateValue v  o) v'

let push env w = resultOfOption InvalidStack (Env.push env) w

let free h a = 
  resultOfOption (UndefinedAddress a) (Heap.free h) a