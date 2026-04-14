open Elab.Proofstate

let test_app_multiarg () =
  let env = Elab.Interface.create () in
  let f, a, b = (mk_name "f", mk_name "a", mk_name "b") in
  let actual_result = mk_app_multiarg f [ a; b ] in
  let expected = mk_app (mk_app f a) b in
  (* TODO: figure out how to use Testable.term for this *)
  Alcotest.(check string)
    "mk_app_multiarg puts arguments in the right order"
    (pp_term env actual_result)
    (pp_term env expected)

let suite =
  let open Alcotest in
  ("Tactic.utils", [ test_case "application multiple arguments" `Quick test_app_multiarg ])
