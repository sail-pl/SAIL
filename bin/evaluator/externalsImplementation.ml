open Saillib.Monad
open Saillib.Heap
open Domain
open ErrorOfOption


let extern h x vl : heap Result.t = 
  let open Result in
  let open MonadSyntax (Result) in
  let open MonadFunctions (Result) in
  match vl with 
    [ v ] when x = "print_string" -> (
      begin match v with
        | VString str ->
          print_string str;
          return h
        | _ -> throwError TypingError
      end)
    | [ v ] when x = "print_int" -> (
      begin match v with
        | VInt str ->
        print_int str;
          return h
        | _ -> throwError TypingError
      end)
  | [] when x = "print_newline" ->
    print_newline ();
    return h
  | [ v1; v2 ] when x = "box" -> (
        match v2 with
    | VLoc (a, o) -> (
        let a', h' = Heap.fresh h in
        let* u = getLocation h a in
        match u with
        | None ->
            let* h'' = setLocation h' (a, Either.Left (VLoc (a', []))) in
            let* h''' = setLocation h'' (a', Either.Left v1) in
            return h'''
        | Some u ->
            let* v0 = resultOfOption TypingError Either.find_left u in
            let* v' = setOffset v0 o v1 in
            let* h'' = setLocation h' (a, Either.Left (VLoc (a', []))) in
            let* h''' = setLocation h'' (a', Either.Left v') in
            return h''')
    | _ -> throwError TypingError)
    | _ -> throwError (UnknownMethod x)