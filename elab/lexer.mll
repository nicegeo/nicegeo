{
open Parser
}

let white = [' ' '\t' '\r']+
let newline = '\n'
let ident = ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '\'']*
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
  | "->"         { FORALL }
  | "=>"         { ARROW }
  | ":"          { COLON }
  | "("          { LPAREN }
  | ")"          { RPAREN }
  | "Type"       { TYPE }
  | "Prop"       { PROP }
  | "_" 	       { UNDERSCORE }
  | "="          { EQUALS }
  | "≠"          { NOT_EQUALS }
  | "<"          { LESS_THAN }
  | "+"          { PLUS }
  | "\\/"        { OR }
  | "/\\"        { AND }
  | "#print"     { PRINT_DIRECTIVE }
  | "#infer"     { INFER_DIRECTIVE }
  | "#check"     { CHECK_DIRECTIVE }
  | "#reduce"    { REDUCE_DIRECTIVE }
  | "#opaque"    { OPAQUE_DIRECTIVE }
  | '"' (string_literal as sl) '"' { STRING_LITERAL sl } (* TODO: Are the quotes necessary? Should we use the raw filepath or something like Lean's modules? *)
  | ident as id  { IDENT id }
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
