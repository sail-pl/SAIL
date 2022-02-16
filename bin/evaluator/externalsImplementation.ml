open Saillib.Monad
open Saillib.Heap
open Domain
open ErrorOfOption

let _print_string = 
  let open Result in 
  let open MonadSyntax (Result) in
  ("print_string", 
    fun h vl -> match vl with [VString str] -> print_string str; return h | _ -> throwError TypingError
  )

let _print_int = 
  let open Result in 
  let open MonadSyntax (Result) in
  ("print_int", 
    fun h vl -> match vl with [VInt i] -> 
      let _ = print_int i in  return h | _ -> throwError TypingError
  )

let _print_newline = 
  let open Result in 
  let open MonadSyntax (Result) in
  ("print_newline", 
    fun h vl -> match vl with [] -> print_newline () ; return h | _ -> throwError TypingError
  )


let _box = 
  let open Result in 
  let open MonadSyntax (Result) in
  ("box", 
    fun h vl -> 
      match vl with [v1; VLoc (a, o, Borrowed (true))] -> 
        let a', h' = Heap.fresh h in
        let* u = getLocation h a in
        let l = VLoc(locationOfAddress a' Owned) in 
        let* v0 = 
          if o = [] then return v1 
          else begin match u with
                | None -> throwError (UnitializedAddress a) 
                | Some u ->
                  let* v0 = resultOfOption TypingError Either.find_left u in
                  setOffset v0 o v1
          end
        in 
          let* h'' = setLocation h' (a, Either.Left l) in 
          let* h''' = setLocation h'' (a', Either.Left v0) in
          return h'''
      | _ -> throwError TypingError
  )

let _drop = 
  let open Result in
  ("drop", 
          fun h vl -> 
            match vl with [VLoc (a,[], Owned)] -> free h a 
            | [VLoc (a,_,_)]  -> throwError (CantDropNotOwned a)
            | _ -> throwError TypingError 
  )

let externals = [_drop; _box; _print_string; _print_int; _print_newline]

let extern h x vl : heap Result.t = 
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  match List.assoc_opt x externals with 
      Some f -> f h vl
    | None -> throwError (UnknownMethod x)
