let () =
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
      Test_proofstate_prefix.suite;
      Test_tactic_utils.suite;
      Test_tactic_choose.suite;
    ]
