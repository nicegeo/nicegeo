%token <string> IDENT STRING_LITERAL
%token FUN FORALL IFF ARROW COLON LPAREN RPAREN TYPE PROP EOF UNDERSCORE PROOF QED PERIOD
%token THEOREM AXIOM DEFINITION DEFEQ IMPORT EQUALS NOT_EQUALS LESS_THAN PLUS NOT OR AND EXISTS COMMA
%token PRINT_DIRECTIVE INFER_DIRECTIVE CHECK_DIRECTIVE REDUCE_DIRECTIVE OPAQUE_DIRECTIVE
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
  | i = import { Statement.Import i }

import:
  | IMPORT fn = STRING_LITERAL { Statement.{filename=fn} }

declaration:
  | AXIOM name = IDENT COLON ty = term { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Axiom} }
  | THEOREM name = IDENT COLON ty = term PROOF proof = list(tactic) QED
    { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Theorem (Proof proof)} }
  | THEOREM name = IDENT COLON ty = term DEFEQ proof = term
    { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Theorem (DefEq proof)} }
  | DEFINITION name = IDENT COLON ty = term DEFEQ body = term
    { Statement.{name=name; name_loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }; ty; kind=Def body} }

tactic:
  | name = IDENT args = list(atomic_term) PERIOD { Statement.{name; args; loc={ Term.start = $startpos(name); Term.end_ = $endpos(name) }} }

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
  | OPAQUE_DIRECTIVE name = IDENT
    { Statement.Opaque (name, { Term.start = $startpos(name); Term.end_ = $endpos(name) }) }

term:
  | t = disjunction_term { t }
  | FUN params = list(param_group) ARROW body = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let params_flat = List.concat params in
      List.fold_right
        (fun (x, ty) acc ->
           let bid = Term.gen_binder_id () in
           {Term.inner=Term.Fun (Some x, bid, ty, Term.subst acc (Term.Name x) (Term.Bvar bid)); loc})
        params_flat body
    }
  | LPAREN x = IDENT COLON ty = term RPAREN FORALL rettype = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let bid = Term.gen_binder_id () in
      {Term.inner=Term.Arrow (Some x, bid, ty, Term.subst rettype (Term.Name x) (Term.Bvar bid)); loc}
    }
  | ty = disjunction_term FORALL rettype = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let bid = Term.gen_binder_id () in
      {Term.inner=Term.Arrow (None, bid, ty, rettype); loc}
    }
  | t1 = disjunction_term IFF t2 = disjunction_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=Name "Iff"; loc}, t1); loc}, t2); loc}
    }
  | EXISTS params = list(param_group) COMMA prop = term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      let params_flat = List.concat params in
      List.fold_right
        (fun (x, ty) acc ->
          let bid = Term.gen_binder_id () in
          let func = Term.{inner=Fun (Some x, bid, ty, subst acc (Name x) (Bvar bid)); loc} in
          Term.{inner=App ({inner=App ({inner=Name "Exists"; loc}, ty); loc}, func); loc}
        )
        params_flat prop
    }

disjunction_term:
  | t = conjunction_term { t }
  | t1 = disjunction_term OR t2 = conjunction_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=Name "Or"; loc}, t1); loc}, t2); loc}
    }

conjunction_term:
  | t = proposition_term { t }
  | t1 = conjunction_term AND t2 = proposition_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=Name "And"; loc}, t1); loc}, t2); loc}
    }

proposition_term:
  | t = sum_term { t }
  | _n = NOT t1 = proposition_term
    {
      let not_loc = { Term.start = $startpos(_n); Term.end_ = $endpos(_n) } in
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=Name "Not"; loc=not_loc}, t1); loc}
    }
  | t1 = sum_term LESS_THAN t2 = sum_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=Name "Lt"; loc}, t1); loc}, t2); loc}
    }
  | t1 = sum_term EQUALS t2 = sum_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=App ({inner=Name "Eq"; loc}, {inner=Hole (gen_hole_id ()); loc}); loc}, t1); loc}, t2); loc}
    }
  | t1 = sum_term NOT_EQUALS t2 = sum_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=App ({inner=Name "Ne"; loc}, {inner=Hole (gen_hole_id ()); loc}); loc}, t1); loc}, t2); loc}
    }

sum_term:
  | t = app_term { t }
  | t1 = sum_term PLUS t2 = app_term
    {
      let loc = { Term.start = $startpos; Term.end_ = $endpos } in
      Term.{inner=App ({inner=App ({inner=Name "Add"; loc}, t1); loc}, t2); loc}
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