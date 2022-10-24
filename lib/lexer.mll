{
  open Lexing
  open Parser

  exception LexError of string
}

(* some definitions of character classes *)

let underscore = '_' (* perhaps we could remove this *)
let prime = '\''
let letter = ['a'-'z' 'A'-'Z']

let digit = ['0'-'9']

let identifier = (letter|underscore|digit)(letter|digit|underscore|prime)*

(* This rule looks for a single line, terminated with '\n' or eof.
   It returns a pair of an optional string (the line that was found)
   and a Boolean flag (false if eof was reached). *)

rule line_comment = parse
| '\n' { new_line lexbuf ; token lexbuf }
| _ { line_comment lexbuf }

and ml_style_block n = parse
| "(*)" { ml_style_block n lexbuf }
| "*)" { if (n-1) = 0 then token lexbuf else ml_style_block (n-1) lexbuf }
| "(*" { ml_style_block (n+1) lexbuf }
| '\n' { new_line lexbuf ; ml_style_block n lexbuf }
| _ { ml_style_block n lexbuf }

and c_style_block = parse
| "*/" { token lexbuf }
| '\n' { new_line lexbuf ; c_style_block lexbuf }
| _ { c_style_block lexbuf }

and token = parse
(* whitespace *)
| ('\t'|' ')+ { token lexbuf }
| ('\n'|'\r') { new_line lexbuf ; token lexbuf }

(* comments and pragmas *)
| "//" { line_comment lexbuf }
(* | "(*#" { PRAGMA_START }
| "#*)" { PRAGMA_END } *)
| "(*)" { line_comment lexbuf }  (* nuScr extension: ml-style line comments *)
| "/*" { c_style_block lexbuf }
| "(*" { ml_style_block 1 lexbuf }

| ['0'-'9']+ as i { INT (int_of_string i) }

(* symbols *)
| ',' { COMMA }
| ';' { SEMICOLON }
| '(' { LPAR }
| ')' { RPAR }
| '{' { LCURLY }
| '}' { RCURLY }

(* keywords *)
| "protocol" { PROTOCOL_KW }
| "global" { GLOBAL_KW }
| "role" { ROLE_KW }
| "from" { FROM_KW }
| "to" { TO_KW }
| "or" { OR_KW }
| "and" { AND_KW }
| "choice" { CHOICE_KW }
| "fin" { FIN_KW }
| "inf" { INF_KW }
| "par" { PAR_KW }
| "intersection" { INTERSECTION_KW }
| "join" { JOIN_KW }
| "prioritise" { PRIORITISE_KW }
| "with" { WITH_KW }
| "high" { HIGH_KW }
| "low" { LOW_KW }

(* other *)
| eof
    { EOI }
| identifier as str { IDENT str }
| _ as unrecog {
  let offset = Lexing.lexeme_start lexbuf in
  let str = Printf.sprintf "At offset %d: unexpected character('%c').\n" offset unrecog in
  LexError str |> raise }
