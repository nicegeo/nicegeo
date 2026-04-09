open Elab.Term
open Elab.Types
open Elab.Proofstate
open Automation.Tactics

let e = Elab.Interface.create ()
let t k = { inner = k; loc = dummy_range }

(* Build a goal state with one hypothesis [name : hyp_ty] and goal type [goal_ty]. *)
let start_with_hyp hyp_name hyp_ty goal_ty =
  let bid = gen_binder_id () in
  let hyp = { hyp_name; hyp_bid = bid; hyp_def = None; hyp_type = hyp_ty } in
  let id = gen_hole_id () in
  Hashtbl.replace e.metas id { ty = Some goal_ty; context = [ bid ]; sol = None };
  let g = { ctx = [ hyp ]; goal_type = goal_ty; goal_id = id } in
  { statement = t (Hole id); open_goals = [ g ]; elab_ctx = e }

(* [h : Sort 1 -> Sort 0], goal [Sort 0]: apply opens one subgoal [Sort 1]. *)
let test_apply_opens_subgoal () =
  let premise = t (Sort 1) in
  let conclusion = t (Sort 0) in
  let arrow_bid = gen_binder_id () in
  let h_ty = t (Arrow (None, arrow_bid, premise, conclusion)) in
  let st = start_with_hyp "h" h_ty conclusion in
  match apply "h" st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' ->
      Alcotest.(check int) "one subgoal remaining" 1 (List.length st'.open_goals);
      Alcotest.(check bool)
        "subgoal type is Sort 1"
        true
        (st'.open_goals |> List.hd |> fun g -> g.goal_type.inner = Sort 1)

(* [h : Sort 0], goal [Sort 0]: no arrow — apply behaves like exact. *)
let test_apply_no_arrow () =
  let st = start_with_hyp "h" (t (Sort 0)) (t (Sort 0)) in
  match apply "h" st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' -> Alcotest.(check bool) "proof complete" true (is_complete st')

(* Conclusion does not match goal — apply should fail. *)
let test_apply_conclusion_mismatch () =
  let arrow_bid = gen_binder_id () in
  let h_ty = t (Arrow (None, arrow_bid, t (Sort 1), t (Sort 1))) in
  let st = start_with_hyp "h" h_ty (t (Sort 0)) in
  let meta_count_before = Hashtbl.length st.elab_ctx.metas in
  match apply "h" st with
  | Success _ -> Alcotest.fail "expected Failure"
  | Failure msg ->
      Alcotest.(check int)
        "failed apply does not leak a fresh meta"
        meta_count_before
        (Hashtbl.length st.elab_ctx.metas);
      Alcotest.(check bool)
        "message mentions apply"
        true
        (String.length msg >= 6 && String.sub msg 0 6 = "apply:")

(* Unknown name should fail with a clear message. *)
let test_apply_unknown_name () =
  let st = init_state ~elab_ctx:e (t (Sort 0)) in
  match apply "no_such_lemma" st with
  | Success _ -> Alcotest.fail "expected Failure"
  | Failure msg ->
      Alcotest.(check string)
        "unknown name message"
        "apply: unknown name 'no_such_lemma'."
        msg

(* No goals remaining: use the no-arrow path to fully close the state, then apply again. *)
let test_apply_no_goals () =
  let st = start_with_hyp "h" (t (Sort 0)) (t (Sort 0)) in
  let st' =
    match apply "h" st with
    | Success s -> s
    | Failure _ -> Alcotest.fail "first apply should succeed"
  in
  match apply "h" st' with
  | Failure msg -> Alcotest.(check string) "no goals message" "No goals remaining." msg
  | Success _ -> Alcotest.fail "expected Failure on completed state"

let suite =
  let open Alcotest in
  ( "Tactic.apply",
    [
      test_case "opens subgoal for premise" `Quick test_apply_opens_subgoal;
      test_case "no arrow behaves like exact" `Quick test_apply_no_arrow;
      test_case "fails on conclusion mismatch" `Quick test_apply_conclusion_mismatch;
      test_case "fails on unknown name" `Quick test_apply_unknown_name;
      test_case "fails when no goals remain" `Quick test_apply_no_goals;
    ] )
