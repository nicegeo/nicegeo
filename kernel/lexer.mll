{
open Parser
}

let white = [' ' '\t' '\n' '\r']+
let ident = ['a'-'z' 'A'-'Z' '_' '.']['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*

rule token = parse
  | white       { token lexbuf }
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
  | ident as id {
      IDENT id
    }
  | eof         { EOF }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | eof         { failwith "Unterminated comment" }
  | _           { comment lexbuf }