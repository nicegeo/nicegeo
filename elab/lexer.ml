open Parser

(* Valid identifier characters, stolen and adapted from Lean *)

(* Letter-like Unicode ranges (Greek, Coptic, etc.) *)
let letter_like_unicode = [%sedlex.regexp?
    0x3B1 .. 0x3C9     |  (* Lower greek *)
    0x391 .. 0x3A9     |  (* Upper greek *)
    0x3CA .. 0x3FB     |  (* Coptic letters *)
    0x1F00 .. 0x1FFE   |  (* Polytonic Greek Extended *)
    0x2100 .. 0x214F   |  (* Letter-like symbols block *)
    0x1D49C .. 0x1D59F    (* Latin Script, Double-struck, Fractur *)
]

(* Subscript and superscript Unicode *)
let subscript_superscript_unicode = [%sedlex.regexp?
    0x207F .. 0x2089  |  (* n superscript and numeric subscripts *)
    0x2090 .. 0x209C  |  (* letter-like subscripts *)
    0x1D62 .. 0x1D6A     (* letter-like subscripts *)
]

(* Characters allowed at the start of an identifier *)
let ident_start = [%sedlex.regexp?
    'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | 
    letter_like_unicode
]

(* Characters allowed in the middle of an identifier *)
let ident_continue = [%sedlex.regexp?
    'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' |
    '\'' | '?' | '!' | '.' |
    letter_like_unicode | subscript_superscript_unicode
]

(* Characters allowed at the end of an identifier, ident_continue without '.' *)
let ident_end = [%sedlex.regexp?
    'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' |
    '\'' | '?' | '!' |
    letter_like_unicode | subscript_superscript_unicode
]

let ident = [%sedlex.regexp? ident_start | ident_start, Star ident_continue, ident_end]
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