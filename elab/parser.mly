%token <string> IDENT
%token FUN FORALL ARROW COLON LPAREN RPAREN TYPE PROP EOF UNDERSCORE
%token THEOREM AXIOM PRIMITIVE DEFEQ
%token PRINT_DIRECTIVE INFER_DIRECTIVE CHECK_DIRECTIVE REDUCE_DIRECTIVE
%start <Statement.statement list> main
%start <Term.term> single_term
%%

main:
  | stmts = list(statement) EOF { stmts }

single_term:
  | t = term EOF { t }

statement:
  | d = declaration { Statement.Declaration d }
  | d = directive { Statement.Directive d }

declaration:
  | AXIOM name = IDENT COLON ty = term { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Axiom} }
  | PRIMITIVE name = IDENT COLON ty = term { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Primitive} }
  | THEOREM name = IDENT COLON ty = term DEFEQ proof = term
    { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Theorem proof} }

directive:
  (* print all axioms used in proposition: #print axioms prop1 *)
  | PRINT_DIRECTIVE _arg = IDENT prop = IDENT
    { Statement.PrintAxioms (prop, { Term.start = $startpos(_arg); Term.end_ = $endpos(prop) }) }
  (* print inferred types in proposition: #infer prop1 *)
  | INFER_DIRECTIVE t = term
    { Statement.Infer (t, { Term.start = $startpos(t); Term.end_ = $endpos(t) }) }
  (* verify term against type: #check (fun (x : Point) => x) : (Point -> Point) *)
  | CHECK_DIRECTIVE t = term COLON ty = term
    { Statement.Check (t, ty, { Term.start = $startpos(t); Term.end_ = $endpos(ty) }) }
  | REDUCE_DIRECTIVE t = term
    { Statement.Reduce (t, { Term.start = $startpos(t); Term.end_ = $endpos(t) }) }

term:
  | t = app_term { t }
  | FUN params = list(param_group) ARROW body = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let params_flat = List.concat params in
      List.fold_right
        (fun (x, ty) acc ->
           let pat = {Term.inner=Term.Name x; loc} in
           {Term.inner=Term.Fun (Some x, ty, Term.bind_bvar acc 0 pat); loc})
        params_flat body
    }
  | LPAREN x = IDENT COLON ty = term RPAREN FORALL rettype = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let pat = {Term.inner=Term.Name x; loc} in
      {Term.inner=Term.Arrow (Some x, ty, Term.bind_bvar rettype 0 pat); loc}
    }
  | ty = app_term FORALL rettype = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      {Term.inner=Term.Arrow (None, ty, rettype); loc}
    }

app_term:
  | t = atomic_term { t }
  | f = app_term arg = atomic_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      {Term.inner=Term.App (f, arg); loc}
    }

atomic_term:
  | UNDERSCORE
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      {Term.inner=Term.Hole (Term.gen_hole_id ()); loc}
    }
  | x = IDENT
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      {Term.inner=Term.Name x; loc}
    }
  | TYPE
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      {Term.inner=Term.Sort 1; loc}
    }
  | PROP
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      {Term.inner=Term.Sort 0; loc}
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
      [(x, {Term.inner=Term.Hole (Term.gen_hole_id ()); loc})]
    }