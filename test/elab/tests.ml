let () =
  let open Alcotest in
  run "elab" [ Test_pretty.suite ]
