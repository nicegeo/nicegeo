open Elab.Statement

let print_term_ast (t : Elab.Term.term) : unit =
  let rec aux (tk : Elab.Term.termkind) : string =
    match tk with
    | Elab.Term.Name s -> Printf.sprintf "Name \"%s\"" s
    | Elab.Term.Bvar i -> Printf.sprintf "Bvar %d" i
    | Elab.Term.Hole i -> Printf.sprintf "Hole %d" i
    | Elab.Term.Fun (name_opt, bid, ty, body) ->
        let name_str = match name_opt with Some n -> Printf.sprintf "Some \"%s\"" n | None -> "None" in
        Printf.sprintf "Fun (%s, %d, %s, %s)" name_str bid (aux ty.inner) (aux body.inner)
    | Elab.Term.Arrow (name_opt, bid, ty_arg, ty_ret) ->
        let name_str = match name_opt with Some n -> Printf.sprintf "Some \"%s\"" n | None -> "None" in
        Printf.sprintf "Arrow (%s, %d, %s, %s)" name_str bid (aux ty_arg.inner) (aux ty_ret.inner)
    | Elab.Term.App (f, arg) ->
        Printf.sprintf "App (%s, %s)" (aux f.inner) (aux arg.inner)
    | Elab.Term.Sort n -> Printf.sprintf "Sort %d" n
  in
  print_endline (aux t.inner)

let print_statement (stmt : Elab.Statement.statement) : unit =
  match stmt with
  | Elab.Statement.Declaration decl ->
      Printf.printf "Declaration: %s\n" decl.name;
      Printf.printf "  type: ";
      print_term_ast decl.ty;
      begin
        match decl.kind with
        | Elab.Statement.Axiom -> Printf.printf "  kind: Axiom\n"
        | Elab.Statement.Def body ->
            Printf.printf "  kind: Def\n";
            Printf.printf "  body: ";
            print_term_ast body
        | Elab.Statement.Theorem (Elab.Statement.DefEq body) ->
            Printf.printf "  kind: Theorem (DefEq)\n";
            Printf.printf "  proof term: ";
            print_term_ast body
        | Elab.Statement.Theorem (Elab.Statement.Proof proof) ->
            Printf.printf "  kind: Theorem (Proof)\n";
            Printf.printf "  proof script tactics: %d\n" (List.length proof.tactics);
            List.iteri
              (fun idx tac ->
                match tac with
                | { Elab.Statement.name; args; _ } ->
                    Printf.printf "    %d: %s " idx name;
                    List.iter (fun arg -> print_term_ast arg; Printf.printf " ") args;
                    Printf.printf "\n")
              proof.tactics
      end
  | Elab.Statement.Directive dir ->
      Printf.printf "Directive: %s\n"
        (match dir with
        | Elab.Statement.PrintAxioms (name, _) -> "PrintAxioms " ^ name
        | Elab.Statement.Infer (_, _) -> "Infer"
        | Elab.Statement.Check (_, _, _) -> "Check"
        | Elab.Statement.Reduce (_, _) -> "Reduce"
        | Elab.Statement.Opaque (name, _) -> "Opaque " ^ name)
  | Elab.Statement.Import import -> Printf.printf "Import: %s\n" import.filename

let () =
  let filename = "/Users/bachhoang/system-e-kernel/test/automation/tests.ncg" in
  print_endline ("Parsing file: " ^ filename);
  let stmts = Elab.Interface.get_all_statements filename in
  List.iteri
    (fun idx stmt ->
      Printf.printf "\n--- statement %d ---\n" idx;
      print_statement stmt)
    stmts
