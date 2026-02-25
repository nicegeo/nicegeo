%token <string> IDENT
%token FUN FORALL ARROW COLON LPAREN RPAREN TYPE PROP EOF UNDERSCORE
%token THEOREM AXIOM DEFEQ
%start <Decl.declaration list> main
%%

main:
  | decls = list(declaration) EOF { decls }

declaration:
  | AXIOM name = IDENT COLON ty = term { Decl.Axiom (name, { Term.start = $startpos(name); Term.end_ = $endpos(name) }, ty) }
  | THEOREM name = IDENT COLON ty = term DEFEQ proof = term
    { Decl.Theorem (name, { Term.start = $startpos(name); Term.end_ = $endpos(name) }, ty, proof) }

term:
  | t = app_term { t }
  | FUN params = list(param_group) ARROW body = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let params_flat = List.concat params in
      List.fold_right
        (fun (x, ty) acc ->
           let pat = (Term.Name x, loc) in
           (Term.Fun (Some x, ty, Term.bind_bvar acc 0 pat), loc))
        params_flat body
    }
  | LPAREN x = IDENT COLON ty = term RPAREN FORALL rettype = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let pat = (Term.Name x, loc) in
      (Term.Arrow (Some x, ty, Term.bind_bvar rettype 0 pat), loc)
    }
  | ty = app_term FORALL rettype = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      (Term.Arrow (None, ty, rettype), loc)
    }

app_term:
  | t = atomic_term { t }
  | f = app_term arg = atomic_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      (Term.App (f, arg), loc)
    }

atomic_term:
  | UNDERSCORE
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      (Term.Hole (Term.gen_hole_id ()), loc)
    }
  | x = IDENT
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      (Term.Name x, loc)
    }
  | TYPE
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      (Term.Sort 1, loc)
    }
  | PROP
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      (Term.Sort 0, loc)
    }
  | LPAREN t = term RPAREN { t }

idlist:
  | x = IDENT { [x] }
  | xs = idlist y = IDENT { xs @ [y] }

param_group:
  | LPAREN xs = idlist COLON ty = term RPAREN { List.map (fun x -> (x, ty)) xs }
  | x = IDENT
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      [(x, (Term.Hole (Term.gen_hole_id ()), loc))]
    }