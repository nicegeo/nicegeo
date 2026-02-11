{
open Parser


let builtins = Hashtbl.to_seq_keys (Env.mk_axioms_env ()) |> List.of_seq
}

let white = [' ' '\t' '\n' '\r']+
let ident = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
  | white       { token lexbuf }
  | "fun"       { FUN }
  | "Claim:"    { CLAIM }
  | "Proof:"    { PROOF }
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