open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Tactics

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

(* dummy tactics for testing combinators *)
let succeed_tac : tactic = fun st -> Success st
let fail_tac    : tactic = fun _  -> Failure "intended failure"

(* ------------------------------------------------------------------ *)
(* Basic combinator tests                                               *)
(* ------------------------------------------------------------------ *)

(** [>>] (seq): succeed_tac passes through, then reflexivity closes. *)
let test_seq () =
  let ctx = setup_env () in
  let st = start ctx (eq_term (name "A") (name "x") (name "x")) in
  match (succeed_tac >> reflexivity) st with
  | Failure msg -> Alcotest.failf "Sequence failed: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof is complete" true (is_complete st')

(** [try_tac]: absorbs a failure and lets the next tactic run. *)
let test_try_tac_absorbs_failure () =
  let ctx = setup_env () in
  let st = start ctx (eq_term (name "A") (name "x") (name "x")) in
  match (try_tac fail_tac >> reflexivity) st with
  | Failure msg -> Alcotest.failf "try_tac should absorb failure: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof complete after try" true (is_complete st')

(** [repeat]: zero applications (tactic fails immediately) is safe. *)
let test_repeat_zero_applications () =
  let ctx = setup_env () in
  let st = start ctx (eq_term (name "A") (name "x") (name "x")) in
  match (repeat fail_tac >> reflexivity) st with
  | Failure msg -> Alcotest.failf "repeat(fail) should be identity: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof complete after repeat" true (is_complete st')

(* ------------------------------------------------------------------ *)
(* Non-trivial combinator tests                                         *)
(* ------------------------------------------------------------------ *)

(** [try_tac] threads state on success (not only on failure). *)
let test_try_tac_threads_state_on_success () =
  let ctx = setup_env () in
  let bid = gen_binder_id () in
  let st = start ctx (t (Arrow (None, bid, name "A", name "A"))) in
  (* try_tac (intro "h") should succeed and advance the state *)
  match try_tac (intro "h") st with
  | Failure msg -> Alcotest.failf "unexpected failure: %s" msg
  | Success st' ->
      let g = List.hd st'.open_goals in
      Alcotest.(check int)    "1 goal remaining after intro"    1 (List.length st'.open_goals);
      Alcotest.(check int)    "context has 1 hypothesis"        1 (List.length g.ctx);
      Alcotest.(check string) "hypothesis name is h"            "h" (List.hd g.ctx).hyp_name

(** [>>] propagates failure from the first tactic without running the second. *)
let test_seq_propagates_first_failure () =
  let ctx = setup_env () in
  let st = start ctx (name "A") in
  (* fail_tac fails, so sorry should never run *)
  let second_ran = ref false in
  let mark_second : tactic = fun st -> second_ran := true; Success st in
  (match (fail_tac >> mark_second) st with
   | Success _ -> Alcotest.fail "expected Failure"
   | Failure msg ->
       Alcotest.(check string) "failure from first tactic" "intended failure" msg;
       Alcotest.(check bool)   "second tactic did not run" false !second_ran)

(** [>>] propagates failure from the second tactic. *)
let test_seq_propagates_second_failure () =
  let ctx = setup_env () in
  let bid = gen_binder_id () in
  let st = start ctx (t (Arrow (None, bid, name "A", name "A"))) in
  (* intro succeeds, but reflexivity then fails (goal A is not Eq ...) *)
  match (intro "h" >> reflexivity) st with
  | Success _ -> Alcotest.fail "expected Failure"
  | Failure msg ->
      Alcotest.(check bool) "failure message from reflexivity" true
        (String.length msg >= 12 && String.sub msg 0 12 = "reflexivity:")

(** [repeat sorry] closes all open subgoals one by one.
    Setup: [have] opens 2 subgoals; [repeat sorry] drains them. *)
let test_repeat_closes_all_subgoals () =
  let ctx = Elab.Interface.create () in
  Hashtbl.add ctx.env "A" { name = "A"; ty = t (Sort 0); data = Axiom };
  Hashtbl.add ctx.env "B" { name = "B"; ty = t (Sort 0); data = Axiom };
  let bid = gen_binder_id () in
  let goal_ty = t (Arrow (None, bid, name "A", name "B")) in
  let st = start ctx goal_ty in
  (* have "x" A opens: goal1=A, goal2=(x:A)→(A→B); repeat sorry drains both *)
  match (have "x" (name "A") >> repeat sorry) st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' ->
      Alcotest.(check bool) "all goals closed by repeat sorry" true (is_complete st')

(** [repeat (intro "h")] on [A → A → A] introduces both premises and stops
    when the goal is no longer an arrow. *)
let test_repeat_intro_exhausts_arrows () =
  let ctx = Elab.Interface.create () in
  Hashtbl.add ctx.env "A" { name = "A"; ty = t (Sort 0); data = Axiom };
  let bid1 = gen_binder_id () in
  let bid2 = gen_binder_id () in
  let goal_ty = t (Arrow (None, bid1, name "A",
                    t (Arrow (None, bid2, name "A", name "A")))) in
  let st = start ctx goal_ty in
  match repeat (intro "h") st with
  | Failure msg -> Alcotest.failf "unexpected failure: %s" msg
  | Success st' ->
      let g = List.hd st'.open_goals in
      Alcotest.(check int)  "2 hypotheses introduced" 2 (List.length g.ctx);
      Alcotest.(check bool) "remaining goal is not an arrow" true
        (match g.goal_type.inner with Arrow _ -> false | _ -> true)

let suite =
  let open Alcotest in
  ( "Tactic.Tacticals",
    [
      test_case "sequence (>>)"                            `Quick test_seq;
      test_case "try_tac absorbs failure"                  `Quick test_try_tac_absorbs_failure;
      test_case "repeat with zero applications"            `Quick test_repeat_zero_applications;
      test_case "try_tac threads state on success"         `Quick test_try_tac_threads_state_on_success;
      test_case ">> propagates first tactic failure"       `Quick test_seq_propagates_first_failure;
      test_case ">> propagates second tactic failure"      `Quick test_seq_propagates_second_failure;
      test_case "repeat sorry closes all subgoals"         `Quick test_repeat_closes_all_subgoals;
      test_case "repeat intro exhausts all arrows"         `Quick test_repeat_intro_exhausts_arrows;
    ] )
