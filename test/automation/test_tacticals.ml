open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Tactics
open Elab.Tactic

let t k = { inner = k; loc = dummy_range }
let name s = t (Name s)
let app f x = t (App (f, x))
let eq_term a lhs rhs = app (app (app (name "Eq") a) lhs) rhs

let setup_env () =
  let ctx = Elab.Interface.create () in
  Hashtbl.add ctx.env "A" { name = "A"; ty = t (Sort 0); data = Axiom };
  Hashtbl.add ctx.env "x" { name = "x"; ty = t (Sort 0); data = Axiom };
  ctx

let start ctx ty = init_state ~elab_ctx:ctx ty

(* dummy tactics for testing *)
let succeed_tac : tactic = fun st -> Success st
let fail_tac : tactic = fun _ -> Failure "intended failure"

(** Test [>>] (seq). [succeed_tac >> reflexivity] should pass through and close the goal
*)
let test_seq () =
  let ctx = setup_env () in
  let goal_ty = eq_term (name "A") (name "x") (name "x") in
  let st = start ctx goal_ty in

  let tac = succeed_tac >> reflexivity in

  match tac st with
  | Failure msg -> Alcotest.failf "Sequence failed: %s" msg
  | Success final_st ->
      Alcotest.(check bool) "proof is complete" true (is_complete final_st)

(** Test [try_tac]. [try_tac fail_tac] should absorb the failure safely and then run
    [reflexivity] *)
let test_try_tac () =
  let ctx = setup_env () in
  let goal_ty = eq_term (name "A") (name "x") (name "x") in
  let st = start ctx goal_ty in

  let tac = try_tac fail_tac >> reflexivity in

  match tac st with
  | Failure msg -> Alcotest.failf "Try failed to absorb failure: %s" msg
  | Success final_st ->
      Alcotest.(check bool) "proof is complete after try" true (is_complete final_st)

(** Test [repeat]. [repeat fail_tac] applies 0 times safely without crashing and then
    [reflexivity] closes the goal *)
let test_repeat () =
  let ctx = setup_env () in
  let goal_ty = eq_term (name "A") (name "x") (name "x") in
  let st = start ctx goal_ty in

  let tac = repeat fail_tac >> reflexivity in

  match tac st with
  | Failure msg -> Alcotest.failf "Repeat failed: %s" msg
  | Success final_st ->
      Alcotest.(check bool) "proof is complete after repeat" true (is_complete final_st)

let suite =
  let open Alcotest in
  ( "Tactic.Tacticals",
    [
      test_case "sequence (>>)" `Quick test_seq;
      test_case "try_tac" `Quick test_try_tac;
      test_case "repeat" `Quick test_repeat;
    ] )
