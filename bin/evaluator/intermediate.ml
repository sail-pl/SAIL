open Common
open Saillib.Heap
open Saillib.Env
open Saillib.MyUtil
open Format

module SailAddress : OrderedValue = struct 

  include Int64

  let pp_t pf i = 
    Format.fprintf pf "%d" (Int64.to_int i)
  let bottom = 0L
  let next = Int64.add 1L
end

type tag = Field of string | Indice of int
type offset = tag list
type location = SailAddress.t * offset

let pp_tag (pf : Format.formatter) (t : tag) : unit =
  match t with 
      Field s -> Format.fprintf pf ".%s" s
    | Indice n -> Format.fprintf pf "[%d]" n

let pp_offset (pf : Format.formatter) (o : offset) : unit =
  Format.fprintf pf "ε%a"
  (Format.pp_print_list ~pp_sep:pp_comma pp_tag)  o

module Location : Value with type t = location = struct 
  type t = location
  let pp_t (pf : Format.formatter) ((a,o) : t) : unit =
    Format.fprintf pf "(%a,%a)" SailAddress.pp_t a pp_offset o
end

module Store = Map.Make(String)

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


let pp_store (pp_a : Format.formatter -> 'a -> unit) (pf : Format.formatter) (fr : 'a Store.t) : unit = 
  Format.fprintf pf "[%a]" (Format.pp_print_list (pp_pair pp_print_string pp_a)) (Store.bindings fr)

let rec pp_value (pf : formatter) (v : value) =
  match v with 
    | VBool b -> Format.pp_print_bool pf b  
    | VInt i -> Format.pp_print_int pf i   
    | VFloat f -> Format.pp_print_float pf f  
    | VChar c -> Format.pp_print_char pf c
    | VString s -> Format.pp_print_string pf s  
    | VArray a -> 
        Format.fprintf pf "[%a]" (Format.pp_print_list ~pp_sep:pp_comma pp_value) a
    | VStruct a -> Format.fprintf pf "<<%a>>" (pp_store pp_value) a
    | VEnum (c, l) -> Format.fprintf pf "%s(%a)" c (Format.pp_print_list ~pp_sep:pp_comma pp_value) l 
    | VLoc l -> Format.fprintf pf "0x%a" Location.pp_t l

module SailHeapValues : Value with type t = (value, bool) sum = struct
  type t = (value, bool) sum
  let pp_t (pf : Format.formatter) (x : t) : unit = 
    match x with 
      | Inl v -> pp_value pf v
      | Inr true -> Format.pp_print_char pf 'P'
      | Inr false -> Format.pp_print_char pf 'A'
end

module SailHeap : Heap with type elt = SailHeapValues.t and type address = SailAddress.t = Heap (SailAddress) (SailHeapValues)

module SailEnv = Env (Location)

type frame = SailEnv.frame
(** Values *)

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

let rec locationsOfValue (v : value) : SailAddress.t list =
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
      | BinOp (u, e1,e2) -> Format.fprintf pf "(%a %s %a)" pp_expression e1 (string_of_binop u) pp_expression e2 
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
  | Seq (c1, c2) -> fprintf pf "%a; %a " pp_command c1 pp_command c2
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

  let rec pp_command_short (pf : formatter) (c : command) : unit =

    match c with 
    | DeclVar (b, x, t) -> 
        if b then fprintf pf "var mut %s : %a" x pp_type t
        else fprintf pf "var %s : %a" x pp_type t
    | DeclSignal (x) -> fprintf pf "signal %s" x
    | Skip -> fprintf pf "skip"
    | Assign (e1, e2) -> fprintf pf "%a := %a" pp_expression e1 pp_expression e2
    | AssignBox (_, _) -> fprintf pf "_ := _"
    | Seq (c1, _) -> fprintf pf "%a; ... " pp_command_short c1
    | Block (_,_) -> fprintf pf "{...}"
    | If (e,_,_) -> fprintf pf "if %a {...} {...}" pp_expression e
    | While (e,_) -> fprintf pf "while %a {...}" pp_expression e
    | Case (e,_) -> fprintf pf "case %a" pp_expression e
    | Invoke (m,el) -> fprintf pf "%s (%a)" m (pp_print_list ~pp_sep:pp_comma pp_expression) el
    | Return -> fprintf pf "return"
    | Emit (s) -> fprintf pf "emit %s" s
    | When (s, _,_) -> fprintf pf "when %s {...}" s
    | Watching (s, _,_) -> fprintf pf "watch %s {...}" s 
    | Par (_, _, _, _) -> fprintf pf "_ || _"