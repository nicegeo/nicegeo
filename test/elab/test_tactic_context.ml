open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Tactics

let t k = { inner = k; loc = dummy_range }
let name s = t (Name s)

let setup_env () =
  let ctx = Elab.Interface.create () in
  Hashtbl.add ctx.env "A" { name = "A"; ty = t (Sort 0); data = Axiom };
  Hashtbl.add ctx.env "B" { name = "B"; ty = t (Sort 0); data = Axiom };
  ctx

let start ctx ty = init_state ~elab_ctx:ctx ty

(* ------------------------------------------------------------------ *)
(* intro tests                                                          *)
(* ------------------------------------------------------------------ *)

(** [intro] should peel off the arrow, push the hypothesis into the
    context, and leave the return type as the new goal. *)
let test_intro_success () =
  let ctx = setup_env () in
  let goal_ty = t (Arrow (Some "x", 0, name "A", name "B")) in
  let st = start ctx goal_ty in
  match intro "h_A" st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' -> (
      match st'.open_goals with
      | [ g ] ->
          Alcotest.(check bool) "goal is B" true
            (match g.goal_type.inner with Name "B" -> true | _ -> false);
          Alcotest.(check int) "context has 1 hypothesis" 1 (List.length g.ctx);
          Alcotest.(check string) "hypothesis name" "h_A" (List.hd g.ctx).hyp_name
      | _ -> Alcotest.fail "expected exactly 1 open goal")

(** [intro] should fail safely if goal is not an implication/forall. *)
let test_intro_failure () =
  let ctx = setup_env () in
  let st = start ctx (name "A") in
  match intro "h" st with
  | Success _ -> Alcotest.fail "expected Failure but intro succeeded on a non-arrow goal"
  | Failure _ -> Alcotest.(check pass) "failed safely" () ()

(** [intro] should fail when there are no goals remaining. *)
let test_intro_no_goals () =
  let ctx = setup_env () in
  let bid = gen_binder_id () in
  let st = start ctx (t (Arrow (None, bid, name "A", name "A"))) in
  let st' = match intro "h" st with
    | Success s -> s
    | Failure _ -> Alcotest.fail "first intro should succeed"
  in
  (* close the remaining goal with sorry, then try intro again *)
  let st'' = match sorry st' with
    | Success s -> s
    | Failure _ -> Alcotest.fail "sorry should succeed"
  in
  match intro "h2" st'' with
  | Failure msg ->
      Alcotest.(check string) "no goals message" "intro: no goals remaining" msg
  | Success _ -> Alcotest.fail "expected Failure on completed state"

(** [intro >> apply] on goal [A → A]: introduce h : A, then close with apply h. *)
let test_intro_apply_identity () =
  let ctx = setup_env () in
  let bid = gen_binder_id () in
  let st = start ctx (t (Arrow (None, bid, name "A", name "A"))) in
  match (intro "h" >> apply "h") st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof complete" true (is_complete st')

(** [intros ["ha"; "hb"]] on [A → B → B] introduces both premises, then
    [apply "hb"] closes the resulting [B] goal. *)
let test_intros_and_apply () =
  let ctx = setup_env () in
  let bid1 = gen_binder_id () in
  let bid2 = gen_binder_id () in
  (* Goal: A → B → B *)
  let goal_ty = t (Arrow (None, bid1, name "A",
                    t (Arrow (None, bid2, name "B", name "B")))) in
  let st = start ctx goal_ty in
  match (intros ["ha"; "hb"] >> apply "hb") st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof complete via intros + apply" true (is_complete st')

(** After [intros ["ha"; "hb"]], the context has both hypotheses in the
    correct order (most recent first). *)
let test_intros_context_order () =
  let ctx = setup_env () in
  let bid1 = gen_binder_id () in
  let bid2 = gen_binder_id () in
  let goal_ty = t (Arrow (None, bid1, name "A",
                    t (Arrow (None, bid2, name "B", name "B")))) in
  let st = start ctx goal_ty in
  match intros ["ha"; "hb"] st with
  | Failure msg -> Alcotest.failf "unexpected failure: %s" msg
  | Success st' ->
      let g = List.hd st'.open_goals in
      Alcotest.(check int)    "ctx has 2 hypotheses" 2 (List.length g.ctx);
      Alcotest.(check string) "innermost hyp is hb" "hb" (List.hd g.ctx).hyp_name;
      Alcotest.(check string) "outer hyp is ha"     "ha" (List.nth g.ctx 1).hyp_name

(* ------------------------------------------------------------------ *)
(* have tests                                                           *)
(* ------------------------------------------------------------------ *)

(** [have] should split the current goal [G] into two subgoals:
    proof of [ty], and the continuation [(name : ty) → G]. *)
let test_have_splits_goal () =
  let ctx = setup_env () in
  let st = start ctx (name "B") in
  match have "h_A" (name "A") st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' -> (
      match st'.open_goals with
      | [ proof_goal; cont_goal ] ->
          Alcotest.(check bool) "first goal is A" true
            (match proof_goal.goal_type.inner with Name "A" -> true | _ -> false);
          Alcotest.(check bool) "second goal is an Arrow" true
            (match cont_goal.goal_type.inner with Arrow _ -> true | _ -> false)
      | _ ->
          Alcotest.failf "expected exactly 2 open goals, got %d"
            (List.length st'.open_goals))

(** Full [have] flow: prove the claim with a concrete term, then use it
    via [intro] + [apply] to close the continuation.

    Setup: env has [myprop : Sort 0] as an axiom.
    Goal: [Sort 0].
    Strategy: [have "x" (Sort 0) >> exact myprop >> intro "x" >> apply "x"]. *)
let test_have_full_flow () =
  let ctx = setup_env () in
  Hashtbl.add ctx.env "myprop" { name = "myprop"; ty = t (Sort 0); data = Axiom };
  let st = start ctx (t (Sort 0)) in
  let tac =
    have "x" (t (Sort 0))
    >> exact (name "myprop")  (* close goal1: prove Sort 0 *)
    >> intro "x"              (* peel (x : Sort 0) → Sort 0 *)
    >> apply "x"              (* x : Sort 0 closes the Sort 0 goal *)
  in
  match tac st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' ->
      Alcotest.(check bool) "have full flow completes proof" true (is_complete st')

(** [have] should fail when there are no goals remaining. *)
let test_have_no_goals () =
  let ctx = setup_env () in
  let st = start ctx (name "A") in
  let st' = match sorry st with
    | Success s -> s
    | Failure _ -> Alcotest.fail "sorry should succeed"
  in
  match have "x" (name "A") st' with
  | Failure msg ->
      Alcotest.(check string) "no goals message" "have: no goals remaining" msg
  | Success _ -> Alcotest.fail "expected Failure on completed state"

let suite =
  let open Alcotest in
  ( "Tactic.Context",
    [
      test_case "intro peels arrow and updates ctx"       `Quick test_intro_success;
      test_case "intro fails on non-arrow"                `Quick test_intro_failure;
      test_case "intro fails when no goals"               `Quick test_intro_no_goals;
      test_case "intro >> apply closes identity proof"    `Quick test_intro_apply_identity;
      test_case "intros + apply closes A→B→B"             `Quick test_intros_and_apply;
      test_case "intros preserves context order"          `Quick test_intros_context_order;
      test_case "have splits goal into proof+continuation"`Quick test_have_splits_goal;
      test_case "have full flow via intro+apply"          `Quick test_have_full_flow;
      test_case "have fails when no goals"                `Quick test_have_no_goals;
    ] )
