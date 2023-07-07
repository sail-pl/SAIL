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

{

  open Lexing
  open Parser
  exception SyntaxError of (position * position) * string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                pos_lnum = pos.pos_lnum + 1
      }

  let pos_range lexbuf = 
    let sp = lexeme_start_p lexbuf and ep = lexeme_end_p lexbuf in 
    sp,ep
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+

let pos = (['1'-'9'] ('_'|digit)*)
let int = '-'? (pos | '0')
let itype = 'i' pos
let float = digit* frac? exp?
let id = (alpha) (alpha|digit|'_')*
let uid = (['A'-'Z']) (alpha|digit|'_')*
let generic_type_param =  (['A'-'Z']) (alpha|digit|'_')*

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read_token = parse 
  | "bool" { TYPE_BOOL }
  | itype { let l = Lexing.lexeme lexbuf in TYPE_INT (int_of_string String.(sub l 1 (length l - 1))) }
  | "int" { TYPE_INT(32)}
  | "float" { TYPE_FLOAT }
  | "char" { TYPE_CHAR}
  | "string" { TYPE_STRING}
  | "type" {TYPE}
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LSQBRACE}
  | "]" { RSQBRACE}
  | "<" { LANGLE }
  | ">" { RANGLE }
  (* | "->" { ARROW } *)
  | "," { COMMA }
  | "." { DOT }
  | ":" { COLON }
  | "::" { DCOLON }
  | ";" { SEMICOLON }
  | "=" { ASSIGN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MUL } 
  | "/" { DIV }
  | "%" { REM }
  | "&"  {REF}
  | "and" { AND }
  | "or" { OR }
  | "||" { PAR }
  | "!" { NOT }
  | "<=" {LE}
  | ">="  {GE}
  | "!=" { NEQ }
  | "==" { EQ }
  | "var" { VAR }
  | "case" {CASE}
  | "signal" { SIGNAL}
  | "struct" { STRUCT }
  | "enum " { ENUM }
  | "process" { PROCESS }
  | "method" { METHOD }
  | "extern" { EXTERN }
  | "import" { IMPORT }
  | "..." { VARARGS }
  | "true" { TRUE }
  | "false" { FALSE }
  | "while" { WHILE }
  | "break" { BREAK }
  | "if" { IF }
  | "else" { ELSE }
  | "return" { RETURN }
  | "await" { AWAIT }
  | "emit" { EMIT }
  | "when" {WHEN}
  | "watching" { WATCHING }
  | "mut" {MUT}
  | "array" {ARRAY}
  | "self" {SELF}
  | "loop" {LOOP}
  | "for" {FOR}
  | "in" {IN}
  | uid { UID (Lexing.lexeme lexbuf) }
  | whitespace { read_token lexbuf }
  | "//" { read_single_line_comment lexbuf }
  | "/*" { read_multi_line_comment lexbuf } 
  | int { INT (Z.of_string (Lexing.lexeme lexbuf |> String.split_on_char '_' |> String.concat ""))}
  | float { FLOAT (float_of_string (Lexing.lexeme lexbuf))}
  | id { ID (Lexing.lexeme lexbuf) }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | "'" {read_char lexbuf}
  | newline { next_line lexbuf; read_token lexbuf }
  | eof { EOF }
  | _ {raise (SyntaxError (pos_range lexbuf, "Lexer - Illegal character: " ^ Lexing.lexeme lexbuf)) }

and read_single_line_comment = parse
  | newline { next_line lexbuf; read_token lexbuf } 
  | eof { EOF }
  | _ { read_single_line_comment lexbuf } 
  
and read_multi_line_comment = parse
  | "*/" { read_token lexbuf } 
  | newline { next_line lexbuf; read_multi_line_comment lexbuf } 
  | eof { raise (SyntaxError (pos_range lexbuf, "Lexer - Unexpected EOF - please terminate your comment.")) }
  | _ { read_multi_line_comment lexbuf } 
and read_char = parse 
  | '\\' '/' '\''  { CHAR '/' }
  | '\\' '\\' '\'' { CHAR '\\'}
  | '\\' 'b'  '\'' { CHAR '\b'}
  | '\\' 'f'  '\'' { CHAR '\012'}
  | '\\' 'n'  '\'' { CHAR '\n'}
  | '\\' 'r'  '\'' { CHAR '\r'}
  | '\\' 't'  '\'' { CHAR '\t'}
  | [^ '"' '\\'] '\'' {CHAR (String.get (Lexing.lexeme lexbuf) 0)}
  | eof { raise (SyntaxError (pos_range lexbuf, "Char is not terminated")) }
  | _ { raise (SyntaxError (pos_range lexbuf, "Illegal character: " ^ Lexing.lexeme lexbuf)) }
and read_string buf = parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError (pos_range lexbuf, "Illegal string character: " ^ Lexing.lexeme lexbuf )) }
  | eof { raise (SyntaxError (pos_range lexbuf, "String is not terminated")) }


  