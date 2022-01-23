open Common
open Saillib.Heap
open Saillib.Env
open Saillib.MyUtil
open Format

module H = Heap 
module Store = Map.Make(String)



type tag = Field of string | Indice of int

type offset = tag list
type location = H.address * offset
type frame = location Env.frame
(** Values *)


type value =
  | VBool of bool
  | VInt of int
  | VFloat of float
  | VChar of char
  | VString of string
  | VArray of value list
  | VStruct of value Store.t
  | VEnum of string * value list
  | VLoc of location


  let valueOfLiteral c =
    match c with
    | LBool x -> VBool x
    | LInt x -> VInt x
    | LFloat x -> VFloat x
    | LChar x -> VChar x
    | LString x -> VString x

let rec readValue (o : offset) (v : value)  : value option =
match (v, o) with
| _, [] -> Some v
| VStruct m, Field f :: o' ->
    Store.find_opt f m >>= readValue o'
| VArray a, Indice n :: o' ->
    List.nth_opt a n >>= readValue o'
| _ -> None

let rec updateValue (v : value) (o : offset) (w : value) : value option =
  match (v, o) with
  | _, [] -> Some w
  | (VStruct m), Field f :: o' ->
      let* v' = Store.find_opt f m in
      let* v0' = updateValue ( v') o' w in
      Some (VStruct (Store.update f (fun _ -> Some v0') m))
  | (VArray a), Indice n :: o' ->
      let* v' = List.nth_opt a n in
      let* v0' = updateValue ( v') o' w in
      Some (VArray (List.mapi (fun i x -> if i = n then v0' else x) a))
  | _ -> None

let rec locationsOfValue (v : value) : H.address list =
  match v with  
    VArray vl -> List.concat (List.map locationsOfValue vl)
  | VStruct m -> List.concat (List.map locationsOfValue (Store.fold (fun _ x y -> x::y) m []))
  | VEnum (_, vl) -> List.concat (List.map locationsOfValue vl)
  | _ -> [] 

type expression =
| Var of string
| Literal of literal
| UnOp of unOp * expression
| BinOp of binOp * expression * expression
| ArrayAlloc of expression list
| ArrayRead of expression * expression
| StructAlloc of expression Store.t
| StructRead of expression * string
| EnumAlloc of string * expression list
| Ref of bool * expression
| Deref of expression


type command =
  | DeclVar of bool * string * sailtype 
  | DeclSignal of string
  | Skip
  | Assign of expression * expression
  | AssignBox of expression * expression
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



let pp_store (pp_a : formatter -> 'a -> unit) (pf : formatter) (m : expression Store.t) =
  Format.pp_print_string pf "[[";
  Store.iter (fun x y -> Format.fprintf pf "%s:%a" x pp_a y) m;
  Format.pp_print_string pf "[["

  let rec pp_expression (pf : formatter) (e : expression) : unit =
    match e with 
        Var x -> Format.fprintf pf "%s" x 
      | Literal c -> Format.fprintf pf "%a" pp_literal c
      | UnOp (u, e) -> Format.fprintf pf "%s%a" (string_of_unop u) pp_expression e
      | BinOp (u, e1,e2) -> Format.fprintf pf "%a%s%a" pp_expression e1 (string_of_binop u) pp_expression e2 
      | ArrayAlloc (el) -> Format.pp_print_list ~pp_sep:pp_comma pp_expression pf el
      | ArrayRead (e1,e2) -> Format.fprintf pf "%a[%a]" pp_expression e1 pp_expression e2
      | StructAlloc(el) -> pp_store pp_expression pf el 
      | StructRead (e, f) -> Format.fprintf pf "%a.%s" pp_expression e f
      | EnumAlloc (c, el) -> Format.fprintf pf "%s(%a)" c (pp_print_list pp_expression) el
      | Ref(b, e) -> 
          if b then Format.fprintf pf "&mut %a" pp_expression e 
          else Format.fprintf pf "& %a" pp_expression e 
      | Deref(e) -> Format.fprintf pf "*%a" pp_expression e 

      let rec pp_command (pf : formatter) (c : command) : unit =
        match c with 
        | DeclVar (b, x, t) -> 
            if b then fprintf pf "var mut %s : %a" x pp_type t
            else fprintf pf "var %s : %a" x pp_type t
        | DeclSignal (x) -> fprintf pf "signal %s" x
        | Skip -> fprintf pf "skip"
        | Assign (e1, e2) -> fprintf pf "%a := %a" pp_expression e1 pp_expression e2
        | AssignBox (_, _) -> fprintf pf "_ := _"
        | Seq (c1, c2) -> fprintf pf "%a;\n%a " pp_command c1 pp_command c2
        | Block (c,_) -> fprintf pf "{%a}" pp_command c
        | If (_,c1,c2) -> fprintf pf "if _ %a %a" pp_command c1 pp_command c2
        | While (_,c) -> fprintf pf "while _ %a" pp_command c
        | Case (_,_) -> fprintf pf "case"
        | Invoke (m,el) -> fprintf pf "%s (%a)" m (pp_print_list ~pp_sep:pp_comma pp_expression) el
        | Return -> fprintf pf "return"
        | Emit (s) -> fprintf pf "emit %s" s
        | When (s, c,_) -> fprintf pf "when %s %a" s pp_command c
        | Watching (s, c,_) -> fprintf pf "watch %s %a" s pp_command c
        | Par (c1, _, c2, _) -> fprintf pf "%a || %a" pp_command c1 pp_command c2