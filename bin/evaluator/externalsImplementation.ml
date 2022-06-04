open Saillib.Monad

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

let _drop = 
  let open Result in
  ("drop", 
          fun h vl -> 
            match vl with 
              [VLoc (a, Owned)] -> free h a 
            | [VLoc (a, Borrowed _)]  -> throwError (CantDropNotOwned a)
            | _ -> throwError TypingError 
  )

let externals = [_drop; (*_box;*) _print_string; _print_int; _print_newline]

let extern h x vl : heap Result.t = 
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  match List.assoc_opt x externals with 
      Some f -> f h vl
    | None -> throwError (UnknownMethod x)
