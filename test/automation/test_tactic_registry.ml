let test_registered_tactics_are_available () =
  let names = Elab.Tactic.registered_tactic_names () in
  let expected =
    [
      "apply";
      "choose";
      "exact";
      "exists";
      "have";
      "intro";
      "intros";
      "left";
      "reflexivity";
      "repeat";
      "rewrite";
      "right";
      "sorry";
      "split";
      "try";
    ]
  in
  List.iter
    (fun name ->
      Alcotest.(check bool)
        (Printf.sprintf "registered tactic '%s'" name)
        true
        (List.mem name names))
    expected;
  Alcotest.(check (list string))
    "tactic names are sorted"
    names
    (List.sort String.compare names)

let suite =
  let open Alcotest in
  ( "Tactic.registry",
    [ test_case "contains default tactics" `Quick test_registered_tactics_are_available ]
  )
