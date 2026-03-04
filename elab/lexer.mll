{
open Parser
}

let white = [' ' '\t' '\r']+
let newline = '\n'
let ident = ['a'-'z' 'A'-'Z' '_' '.']['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*

rule token = parse
  | white       { token lexbuf }
  | newline     { Lexing.new_line lexbuf; token lexbuf }
  | "(*"        { comment lexbuf; token lexbuf }
  | "fun"       { FUN }
  | "Axiom"     { AXIOM }
  | "Theorem"   { THEOREM }
  | ":="        { DEFEQ }
  | "->"        { FORALL }
  | "=>"        { ARROW }
  | ":"         { COLON }
  | "("         { LPAREN }
  | ")"         { RPAREN }
  | "Type"      { TYPE }
  | "Prop"      { PROP }
  | "_" 	    { UNDERSCORE }
  | ident as id {
      IDENT id
    }
  | eof         { EOF }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | eof         { failwith "Unterminated comment" }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | _           { comment lexbuf }