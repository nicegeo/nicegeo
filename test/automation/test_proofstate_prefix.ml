open Elab

let path_to_env = "env.ncg"

let suite =
  let open Alcotest in
  ( "proofstate_prefix",
    [
      test_case "cursor before tactic end keeps initial goal" `Quick (fun () ->
          let env = Interface.create () in
          Interface.process_file env path_to_env;
          let src =
            "Theorem t : (A: Type) -> A -> A\nProof.\nintros A a.\nexact a.\nQed."
          in
          let lexbuf = Sedlexing.Utf8.from_string src in
          Sedlexing.set_filename lexbuf "virtual.ncg";
          let parse = MenhirLib.Convert.Simplified.traditional2revised Parser.main in
          let stmts = parse (Sedlexing.with_tokenizer Lexer.token lexbuf) in
          let decl =
            match stmts with
            | [ Statement.Declaration d ] -> d
            | _ -> Alcotest.fail "expected single declaration"
          in
          let goal_ty = Typecheck.elaborate env decl.ty None in
          let init_st = Proofstate.init_state ~elab_ctx:env goal_ty in
          let tacs =
            match decl.kind with
            | Statement.Theorem (Statement.Proof ps) -> ps.tactics
            | _ -> Alcotest.fail "expected Proof script"
          in
          let st0 = Tactic.apply_first_k_tactics init_st tacs 0 in
          let st1 = Tactic.apply_first_k_tactics init_st tacs 1 in
          let g0 = List.hd st0.open_goals in
          let g1 = List.hd st1.open_goals in
          let s0 = Pretty.term_to_string st0.elab_ctx g0.goal_type in
          let s1 = Pretty.term_to_string st1.elab_ctx g1.goal_type in
          check string "k=0 goal" "(A : Type) → A → A" s0;
          check int "k=0 hyps" 0 (List.length g0.lctx);
          check int "k=1 hyps" 2 (List.length g1.lctx);
          if String.equal s0 s1 then Alcotest.fail "goal should change after first tactic");
    ] )
