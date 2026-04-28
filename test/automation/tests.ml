let () =
  (* run test file *)
  Automation.Tactics.register ();
  let env = Elab.Interface.create () in
  (try Elab.Interface.process_file env "env.ncg"
   with Elab.Error.ElabError info ->
     print_endline
       ("Internal error while processing env.ncg: " ^ Elab.Error.pp_exn env info);
     exit 255);
  (try Elab.Interface.process_file env "tests.ncg"
   with Elab.Error.ElabError info ->
     print_endline ("Error processing tests.ncg:\n" ^ Elab.Error.pp_exn env info);
     exit 255);

  let open Alcotest in
  run
    "automation"
    [
      Test_tactic_refl.suite;
      Test_tactic_sorry.suite;
      Test_tactic_exact.suite;
      Test_tactic_apply.suite;
      Test_tacticals.suite;
      Test_tactic_context.suite;
      Test_tactic_rw.suite;
      Test_tactic_exists.suite;
      Test_tactic_construct_or.suite;
      Test_proofstate_prefix.suite;
      Test_tactic_split.suite;
      Test_tactic_utils.suite;
      Test_tactic_choose.suite;
      Test_measure.suite;
      Test_fm_elim.suite;
    ]
