open Elab.Term
open Elab.Proofstate
open Elab.Tactics

let e = Elab.Interface.create ()
let t k = { inner = k; loc = dummy_range }
let name s = t (Name s)
let start ty = init_state ~elab_ctx:e ty

let test_sorry_closes_goal () =
  let st = start (name "P") in
  match sorry st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof is complete after sorry" true (is_complete st')

let test_sorry_any_shape () =
  let goal = t (Arrow (Some "x", 0, name "A", name "B")) in
  let st = start goal in
  match sorry st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' -> Alcotest.(check bool) "proof complete" true (is_complete st')

let test_sorry_no_goals () =
  let st = start (name "P") in
  let st' =
    match sorry st with
    | Success s -> s
    | Failure _ -> Alcotest.fail "first sorry should succeed"
  in
  match sorry st' with
  | Failure msg -> Alcotest.(check string) "no goals message" "No goals remaining." msg
  | Success _ -> Alcotest.fail "expected Failure on completed state"

let suite =
  let open Alcotest in
  ( "Tactic.sorry",
    [
      test_case "closes any goal" `Quick test_sorry_closes_goal;
      test_case "closes any-shape goal" `Quick test_sorry_any_shape;
      test_case "fails when no goals" `Quick test_sorry_no_goals;
    ] )
