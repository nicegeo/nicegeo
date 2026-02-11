{
open Parser


let builtins = Hashtbl.to_seq_keys (Env.mk_axioms_env ()) |> List.of_seq
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
    if List.mem id builtins then
        CONST id
    else 
        IDENT id
    }
  | eof         { EOF }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | eof         { failwith "Unterminated comment" }
  | _           { comment lexbuf }