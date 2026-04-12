{
open Parser
open Lexing
(* Shift the file location information tracked by lexbuf back by n. This is necessary for correct file 
locations in error messages because ocamllex is unicode-blind. For k-byte unicode characters that are 
visually a single character, ocamllex shifts the position forward by k, so we shift it back by k-1. *)
let shift_pos lexbuf n =
  (* HACK: the generated lexer.ml calls Lexing.engine which hard-codes the update to pos_cnum, so 
  without changing the generated lexer it is essentially tied to the byte position of the file. Instead,
  we modify pos_bol, intended to be the byte offset of the current line, but as far as I can tell it is
  not used anywhere by the lexer or parser (which just passes the position information). So we 
  reinterpret the pos_bol field as "byte offset into file - visual offset into line" for error messages, 
  which needs to be updated whenever the visual offset changes relative to the byte offset (i.e. whenever
  there's a unicode character) by however many extra bytes the unicode character takes up. *)
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_bol = lexbuf.lex_curr_p.pos_bol + n }
}

let white = [' ' '\t' '\r']+
let newline = '\n'
let ident = ['a'-'z' 'A'-'Z' '0'-'9' '_'] | ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '\'']*['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let string_literal = ['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '/']*
(* Ocamllex doesn't apparently have native support for UTF-8 since it just views the input as a sequence
  of bytes and applies the regular expressions to that (see https://stackoverflow.com/questions/76579864/specifying-ocamllex-encoding)
  so we have to define a regular expression like this to recognize when there's a non-ASCII character *)
(* Write a regular expression for a single UTF-8 codepoint so that the error message actually shows the full
  character instead of just the first byte (since the first byte is just some byte that's greater than 0x80 which
  isn't very easy to understand) *)
let utf8_continuation_byte = ['\x80' - '\xBF']
let utf8_codepoint = 
  ['\x00' - '\x7F'] |
  (['\xc0' - '\xdf'] utf8_continuation_byte) |
  (['\xe0' - '\xef'] utf8_continuation_byte utf8_continuation_byte) |
  (['\xf0' - '\xff'] utf8_continuation_byte utf8_continuation_byte utf8_continuation_byte)

rule token = parse
  | white        { token lexbuf }
  | newline      { Lexing.new_line lexbuf; token lexbuf }
  | "(*"         { comment lexbuf; token lexbuf }
  | "fun"        { FUN }
  | "Axiom"      { AXIOM }
  | "Theorem"    { THEOREM }
  | "Definition" { DEFINITION }
  | "Import"     { IMPORT }
  | ":="         { DEFEQ }
  | "->"         { ARROW }
  | "→"          { shift_pos lexbuf 2; ARROW }
  | "<->"        { IFF }
  | "↔"          { shift_pos lexbuf 2; IFF }
  | "=>"         { MAPSTO }
  | ":"          { COLON }
  | "("          { LPAREN }
  | ")"          { RPAREN }
  | "Type"       { TYPE }
  | "Prop"       { PROP }
  | "_" 	       { UNDERSCORE }
  | "="          { EQUALS }
  | "≠"          { shift_pos lexbuf 2; NOT_EQUALS }
  | "<"          { LESS_THAN }
  | "+"          { PLUS }
  | "\\/"        { OR }
  | "∨"          { shift_pos lexbuf 2; OR }
  | "/\\"        { AND }
  | "∧"          { shift_pos lexbuf 2; AND }
  | "~"          { NOT }
  | "¬"          { shift_pos lexbuf 1; NOT }
  | "∃"          { shift_pos lexbuf 2; EXISTS }
  | "∀"          { shift_pos lexbuf 2; FORALL }
  | ","          { COMMA }
  | "#print"     { PRINT_DIRECTIVE }
  | "#infer"     { INFER_DIRECTIVE }
  | "#check"     { CHECK_DIRECTIVE }
  | "#reduce"    { REDUCE_DIRECTIVE }
  | "#opaque"    { OPAQUE_DIRECTIVE }
  | '"' (string_literal as sl) '"' { STRING_LITERAL sl } (* TODO: Are the quotes necessary? Should we use the raw filepath or something like Lean's modules? *)
  | ident as id  { IDENT id }
  | "Proof."     { PROOF }
  | "Qed."       { QED }
  | "."          { PERIOD }
  | eof          { EOF }
  (* TODO: maybe display bytes in hexadecimal instead of decimal (since using '\123' in a decent number of languages (e.g. C, Python)
    usually means to interpret that number in octal, not decimal, so that notation might confuse people) *)
  | utf8_codepoint as s { failwith (Printf.sprintf "expected input to be ASCII but found non-ASCII bytes %S" s) }
  | _ as c { failwith (Printf.sprintf "unexpected character: '\\x%X'" (Char.code c)) }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | eof         { failwith "Unterminated comment" }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | _           { comment lexbuf }
