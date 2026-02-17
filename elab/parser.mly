%token <string> IDENT
%token FUN FORALL ARROW COLON LPAREN RPAREN TYPE PROP EOF UNDERSCORE
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
  | FUN params = list(param_group) ARROW body = term
    {
      let params_flat = List.concat params in
      List.fold_right (fun (x,ty) acc -> Term.Fun (x, ty, acc)) params_flat body
    }
  | LPAREN x = IDENT COLON ty = term RPAREN FORALL rettype = term
    { Term.Arrow (x, ty, rettype) }
  | ty = app_term FORALL body = term
    { Term.Arrow ("", ty, body) }

app_term:
  | t = atomic_term { t }
  | f = app_term arg = atomic_term { Term.App (f, arg) }

atomic_term:
  | UNDERSCORE { Term.Hole }
  | x = IDENT { Term.Name x }
  | TYPE { Term.Sort 1 }
  | PROP { Term.Sort 0 }
  | LPAREN t = term RPAREN { t }

idlist:
  | x = IDENT { [x] }
  | xs = idlist y = IDENT { xs @ [y] }

param_group:
  | LPAREN x = IDENT COLON ty = term RPAREN { [ (x, ty) ] }
  | LPAREN xs = idlist COLON ty = term RPAREN { List.map (fun x -> (x, ty)) xs }