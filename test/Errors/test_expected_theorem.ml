let () =
  let env = Elab.Interface.create_with_env () in
  Elab.Interface.process_file env "test/Errors/expected_theorem.elab";
  try
    let _ = Elab.Interface.list_axioms env "only_axiom" in
    print_endline "Unexpected success"
  with Error.ElabError e -> print_endline (Error.pp_exn env e)
