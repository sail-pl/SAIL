open Common
open Saillib.Pp_util
open Saillib.Heap
open Domain
open Format

let pp_print_tag (pf : Format.formatter) (t : Domain.tag) : unit =
  match t with
  | Field s -> Format.fprintf pf ".%s" s
  | Indice n -> Format.fprintf pf "[%d]" n

let pp_print_offset (pf : Format.formatter) (o : Domain.offset) : unit =
  Format.fprintf pf "ε%a" (Format.pp_print_list ~pp_sep:pp_comma pp_print_tag) o

let pp_print_location pf (a, o) =
  Format.fprintf pf "(%a,%a)" Heap.pp_address a pp_print_offset o

let rec pp_print_value (pf : Format.formatter) (v : Domain.value) =
  match v with
  | VBool b -> Format.pp_print_bool pf b
  | VInt i -> Format.pp_print_int pf i
  | VFloat f -> Format.pp_print_float pf f
  | VChar c -> Format.pp_print_char pf c
  | VString s -> Format.pp_print_string pf s
  | VArray a ->
      Format.fprintf pf "[%a]"
        (Format.pp_print_list ~pp_sep:pp_comma pp_print_value)
        a
  | VStruct a -> 
      Format.fprintf pf "{%a}"
        (Format.pp_print_list ~pp_sep:pp_comma (pp_print_pair pp_print_string pp_print_value))
        (FieldMap.bindings a) 
  | VEnum (c, l) ->
      Format.fprintf pf "%s(%a)" c
        (Format.pp_print_list ~pp_sep:pp_comma pp_print_value)
        l
  | VLoc l -> Format.fprintf pf "0x%a" pp_print_location l

let pp_print_heapValue pf v =
  match v with Either.Left v -> pp_print_value pf v | Either.Right b -> Format.pp_print_bool pf b

let pp_print_expression pf e : unit =
  let rec aux pf e =
    match e with
    | Var x -> Format.pp_print_string pf x
    | Literal c -> Format.fprintf pf "%a" Common.pp_literal c
    | UnOp (op, e) -> Format.fprintf pf "%a%a" Common.pp_unop op aux e
    | BinOp (op, e1, e2) ->
        Format.fprintf pf "(%a %a %a)" aux e1 Common.pp_binop op aux e2
    | ArrayAlloc el ->
        Format.fprintf pf "[%a]"
          (Format.pp_print_list ~pp_sep:Common.pp_comma aux)
          el
    | ArrayRead (e1, e2) -> Format.fprintf pf "%a[%a]" aux e1 aux e2
    | StructAlloc m ->
        let pp_field pf (x, y) = Format.fprintf pf "%s:%a" x aux y in
        Format.fprintf pf "{%a}"
          (Format.pp_print_list ~pp_sep:Common.pp_comma pp_field)
          (FieldMap.bindings m)
    | StructRead (e, f) -> Format.fprintf pf "%a.%s" aux e f
    | EnumAlloc (c, el) ->
        Format.fprintf pf "%s(%a)" c
          (Format.pp_print_list ~pp_sep:Common.pp_comma aux)
          el
    | Ref (b, e) ->
        if b then Format.fprintf pf "&mut %a" aux e
        else Format.fprintf pf "& %a" aux e
    | Deref e -> Format.fprintf pf "* %a" aux e
  in
  aux pf e

let rec pp_print_command (pf : Format.formatter) (c : command) : unit =
  match c with
  | DeclVar (b, x, t) ->
      if b then Format.fprintf pf "var mut %s : %a;" x Common.pp_type t
      else Format.fprintf pf "var %s : %a;" x Common.pp_type t
  | DeclSignal x -> Format.fprintf pf "signal %s;" x
  | Skip -> Format.fprintf pf "skip;"
  | Assign (e1, e2) ->
      Format.fprintf pf "%a = %a;" pp_print_expression e1 pp_print_expression e2
  | Seq (c1, c2) -> Format.fprintf pf "%a; %a " pp_print_command c1 pp_print_command c2
  | Block (c, _) -> Format.fprintf pf "{%a}" pp_print_command c
  | If (e, c1, c2) ->
      Format.fprintf pf "if (%a) %a %a" pp_print_expression e pp_print_command c1 pp_print_command
        c2
  | While (e, c) ->
      Format.fprintf pf "while (%a) %a" pp_print_expression e pp_print_command c
  | Case (e, pl) ->
      let pp_case (pf : Format.formatter) ((p, c) : Common.pattern * command) =
        Format.fprintf pf "%a:%a" Common.pp_pattern p pp_print_command c
      in
      Format.fprintf pf "case (%a) {%a}" pp_print_expression e
        (Format.pp_print_list ~pp_sep:Common.pp_comma pp_case)
        pl
  | Invoke (m, el) ->
      Format.fprintf pf "%s (%a);" m
        (Format.pp_print_list ~pp_sep:Common.pp_comma pp_print_expression)
        el
  | Return -> Format.fprintf pf "return;"
  | Emit s -> Format.fprintf pf "emit %s;" s
  | When (s, c, _) -> Format.fprintf pf "when %s {%a}" s pp_print_command c
  | Watching (s, c, _) -> Format.fprintf pf "watch %s {%a}" s pp_print_command c
  | Par (c1, _, c2, _) ->
      Format.fprintf pf "%a || %a" pp_print_command c1 pp_print_command c2

let rec pp_command_short (pf : Format.formatter) (c : command) : unit =
  let open Format in
  match c with
  | DeclVar (b, x, t) ->
      if b then Format.fprintf pf "var mut %s : %a" x Common.pp_type t
      else Format.fprintf pf "var %s : %a" x Common.pp_type t
  | DeclSignal x -> Format.fprintf pf "signal %s" x
  | Skip -> Format.fprintf pf "skip"
  | Assign (e1, e2) ->
      Format.fprintf pf "%a := %a" pp_print_expression e1 pp_print_expression e2
  | Seq (c1, _) -> Format.fprintf pf "%a; ... " pp_command_short c1
  | Block (_, _) -> Format.fprintf pf "{...}"
  | If (e, _, _) -> Format.fprintf pf "if %a {...} {...}" pp_print_expression e
  | While (e, _) -> Format.fprintf pf "while %a {...}" pp_print_expression e
  | Case (e, _) -> Format.fprintf pf "case %a" pp_print_expression e
  | Invoke (m, el) ->
      Format.fprintf pf "%s (%a)" m
        (pp_print_list ~pp_sep:Common.pp_comma pp_print_expression)
        el
  | Return -> Format.fprintf pf "return"
  | Emit s -> Format.fprintf pf "emit %s" s
  | When (s, _, _) -> Format.fprintf pf "when %s {...}" s
  | Watching (s, _, _) -> Format.fprintf pf "watch %s {...}" s
  | Par (_, _, _, _) -> Format.fprintf pf "_ || _"

let pp_print_result (pf : Format.formatter) (r : command status) : unit =
  match r with
  | Ret -> Format.fprintf pf "ret"
  | Continue -> Format.fprintf pf "continue"
  | Suspend c -> pp_print_command pf c

  let pp_print_error (pf : Format.formatter) (e : Domain.error) : unit =
    match e with 
      | TypingError -> Format.pp_print_string pf "Type error"
      | UnknownMethod (m) -> Format.fprintf pf "Unknown method %s" m
      | UnknownVariable (x) -> Format.fprintf pf "Unknown variable %s" x
      | UnknownField (f) -> Format.fprintf pf "Unknown field %s" f
      | UnknownSignal (s) -> Format.fprintf pf "Unknown signal %s" s
      | UndefinedOffset (v, o) -> Format.fprintf pf "Unknown field %a in %a" pp_print_offset o pp_print_value v
      | UndefinedAddress (a) -> Format.fprintf pf "Undefined address %a" Heap.pp_address a
      | UnitializedAddress (a) -> Format.fprintf pf "Uninitialized address %a" Heap.pp_address a
      | OutOfBounds (n) -> Format.fprintf pf "Out of bound index %d" n
      | IncompletePatternMatching (v) -> Format.fprintf pf "Incomplete pattern matching %a" pp_print_value v
      | MissingReturnStatement -> Format.pp_print_string pf "Missing return statement in method"
      | ReturnStatementInProcess -> Format.pp_print_string pf "Forbidden return statement in process"
      | NotASignalState -> Format.pp_print_string pf "Not a signal state"
      | InvalidStack -> Format.pp_print_string pf "Invalid Stack"
      | NotALeftValue -> Format.pp_print_string pf "Not A left value"
      | NotAValue -> Format.pp_print_string pf "Not a value"
      | Division_by_zero -> Format.pp_print_string pf "Division by zero"
    