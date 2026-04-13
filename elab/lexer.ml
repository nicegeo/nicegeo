open Parser

let ident_char = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | 0x80 .. 0x10FFFF]
let ident_mid_char = [%sedlex.regexp? ident_char | '.' | '\'']
let ident_end_char = [%sedlex.regexp? ident_char | '\'']
let ident = [%sedlex.regexp? ident_char | ident_char, Star ident_mid_char, ident_end_char]
let string_char = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '.' | '/']

let token lexbuf =
  let rec token lexbuf =
    match%sedlex lexbuf with
    | Plus (' ' | '\t' | '\r' | '\n') -> token lexbuf
    | "(*" ->
        comment lexbuf;
        token lexbuf
    | "fun" -> FUN
    | "Axiom" -> AXIOM
    | "Theorem" -> THEOREM
    | "Definition" -> DEFINITION
    | "Import" -> IMPORT
    | ":=" -> DEFEQ
    | "->" | Utf8 "→" -> ARROW
    | "<->" | Utf8 "↔" -> IFF
    | "=>" -> MAPSTO
    | ":" -> COLON
    | "(" -> LPAREN
    | ")" -> RPAREN
    | "Type" -> TYPE
    | "Prop" -> PROP
    | "_" -> UNDERSCORE
    | "=" -> EQUALS
    | Utf8 "≠" -> NOT_EQUALS
    | "<" -> LESS_THAN
    | "+" -> PLUS
    | "\\/" | Utf8 "∨" -> OR
    | "/\\" | Utf8 "∧" -> AND
    | "~" | Utf8 "¬" -> NOT
    | Utf8 "∃" -> EXISTS
    | Utf8 "∀" -> FORALL
    | "," -> COMMA
    | "#print" -> PRINT_DIRECTIVE
    | "#infer" -> INFER_DIRECTIVE
    | "#check" -> CHECK_DIRECTIVE
    | "#reduce" -> REDUCE_DIRECTIVE
    | "#opaque" -> OPAQUE_DIRECTIVE
    | '"', Star string_char, '"' ->
        let s = Sedlexing.Utf8.lexeme lexbuf in
        let len = String.length s in
        STRING_LITERAL (String.sub s 1 (len - 2))
    | ident -> IDENT (Sedlexing.Utf8.lexeme lexbuf)
    | "Proof." -> PROOF
    | "Qed." -> QED
    | "." -> PERIOD
    | eof -> EOF
    | any ->
        let bad = Sedlexing.Utf8.lexeme lexbuf in
        failwith (Printf.sprintf "unexpected character: %S" bad)
    | _ ->
        failwith "unreachable"
  and comment lexbuf =
    match%sedlex lexbuf with
    | "*)" -> ()
    | "(*" ->
        comment lexbuf;
        comment lexbuf
    | eof -> failwith "Unterminated comment"
    | any -> comment lexbuf
    | _ -> failwith "unreachable"
  in
  token lexbuf