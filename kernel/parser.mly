%token <string> IDENT
%token FUN FORALL ARROW COLON LPAREN RPAREN TYPE PROP EOF
%token THEOREM AXIOM DEFEQ
%start <Decl.declaration list> main
%%

main:
  | decls = list(declaration) EOF { decls }

declaration:
  | AXIOM name = IDENT COLON ty = term { Decl.Axiom (name, ty) }
  | THEOREM name = IDENT COLON ty = term DEFEQ proof = term
    { Decl.Theorem (name, ty, proof) }

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
  | TYPE { Term.Sort 1 }
  | PROP { Term.Sort 0 }
  | LPAREN t = term RPAREN { t }