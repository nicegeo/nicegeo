let () =
  let open Alcotest in
  run
    "elab"
    [
      Test_pretty.suite;
      Test_kernel_pretty.suite;
      Test_nice_messages.suite;
      Test_interface.suite;
      Test_tactic_refl.suite;
      Test_tactic_sorry.suite;
      Test_tactic_exact.suite;
      Test_tactic_apply.suite;
      Test_tacticals.suite;
    ]
