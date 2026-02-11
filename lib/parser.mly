%token <string> IDENT
%token <string> CONST
%token FUN FORALL ARROW COLON LPAREN RPAREN TYPE PROP EOF
%token CLAIM PROOF
%start <Term.term * Term.term> main
%%

main:
  | CLAIM claim_term = term PROOF proof_term = term EOF
    { (claim_term, proof_term) }

term:
  | t = app_term { t }
  | FUN LPAREN x = IDENT COLON ty = term RPAREN ARROW body = term
    { Term.Lam (ty, Infer.rebind_bvar body 0 x) }
  | LPAREN x = IDENT COLON ty = term RPAREN FORALL body = term
    { Term.Forall (ty, Infer.rebind_bvar body 0 x) }
  | ty = app_term FORALL body = term
    { Term.Forall (ty, body) }

app_term:
  | t = atomic_term { t }
  | f = app_term arg = atomic_term { Term.App (f, arg) }

atomic_term:
  | x = IDENT { Term.Fvar x }
  | c = CONST { Term.Const c }
  | TYPE { Term.Sort 0 }
  | PROP { Term.Sort 0 }
  | LPAREN t = term RPAREN { t }