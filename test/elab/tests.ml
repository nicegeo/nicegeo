let () =
  let open Alcotest in
  run "elab" [ Test_pretty.suite; Test_kernel_pretty.suite; Test_nice_messages.suite ]
