{

  open Lexing
  open Parser

  exception SyntaxError of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                pos_lnum = pos.pos_lnum + 1
      }
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+

let int = '-'? digit+
let float = digit* frac? exp?
let id = (alpha) (alpha|digit|'_')*
let uid = (['A'-'Z']) (alpha|digit|'_')*
let generic_type_param =  (['A'-'Z']) (alpha|digit|'_')*

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read_token = parse 
  | "bool" { TYPE_BOOL }
  | "int" { TYPE_INT }
  | "float" { TYPE_FLOAT }
  | "char" { TYPE_CHAR}
  | "string" { TYPE_STRING}
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LSQBRACE}
  | "]" { RSQBRACE}
  | "<" { LANGLE }
  | ">" { RANGLE }
  | "," { COMMA }
  | "." { DOT }
  | ":" { COLON }
  | ";" { SEMICOLON }
  | "=" { ASSIGN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MUL } 
  | "/" { DIV }
  | "%" { REM }
  | "&"  {REF}
  | "&&" { AND }
  | "||" { OR }
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
  | "true" { TRUE }
  | "false" { FALSE }
  | "while" { WHILE }
  | "if" { IF }
  | "else" { ELSE }
  | "return" { RETURN }
  | "await" { AWAIT }
  | "emit" { EMIT }
  | "when" {WHEN}
  | "watching" { WATCHING }
  | "mut" {MUT}
  | "array" {ARRAY}
  | uid { UID (Lexing.lexeme lexbuf) }
  | whitespace { read_token lexbuf }
  | "//" { read_single_line_comment lexbuf }
  | "/*" { read_multi_line_comment lexbuf } 
  | int { INT (int_of_string (Lexing.lexeme lexbuf))}
  | id { ID (Lexing.lexeme lexbuf) }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | "'" {QUOTE}
  | alpha {CHAR (String.get (Lexing.lexeme lexbuf) 0)}
  | newline { next_line lexbuf; read_token lexbuf }
  | eof { EOF }
  | _ {raise (SyntaxError ("Lexer - Illegal character: " ^ Lexing.lexeme lexbuf)) }

and read_single_line_comment = parse
  | newline { next_line lexbuf; read_token lexbuf } 
  | eof { EOF }
  | _ { read_single_line_comment lexbuf } 
  
and read_multi_line_comment = parse
  | "*/" { read_token lexbuf } 
  | newline { next_line lexbuf; read_multi_line_comment lexbuf } 
  | eof { raise (SyntaxError ("Lexer - Unexpected EOF - please terminate your comment.")) }
  | _ { read_multi_line_comment lexbuf } 
  
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
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }


