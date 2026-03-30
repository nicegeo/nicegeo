open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Tactics

let e = Elab.Interface.create ()

let t k = { inner = k; loc = dummy_range }

let start ty = init_state ~elab_ctx:e ty

(* Sort 0 : Sort 1, so [exact (Sort 0)] closes a goal of type [Sort 1]. *)
let test_exact_sort () =
  let st = start (t (Sort 1)) in
  match exact (t (Sort 0)) st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof complete after exact" true (is_complete st')

(* [Sort 0] has type [Sort 1], not [Sort 0], so this should fail. *)
let test_exact_wrong_type () =
  let st = start (t (Sort 0)) in
  match exact (t (Sort 0)) st with
  | Success _ -> Alcotest.fail "expected Failure but got Success"
  | Failure msg ->
      Alcotest.(check bool) "message starts with 'exact:'"
        true (String.length msg >= 6 && String.sub msg 0 6 = "exact:")

(* [exact] with a hypothesis: goal is [h : Sort 0 |- Sort 0], proof is [Bvar bid]. *)
let test_exact_hyp () =
  let bid = gen_binder_id () in
  let hyp_ty = t (Sort 0) in
  let hyp = { hyp_name = "h"; hyp_bid = bid; hyp_def = None; hyp_type = hyp_ty } in
  let id = gen_hole_id () in
  Hashtbl.replace e.metas id { ty = Some hyp_ty; context = [bid]; sol = None };
  let g = { ctx = [hyp]; goal_type = hyp_ty; goal_id = id } in
  let st = { statement = t (Hole id); open_goals = [g]; elab_ctx = e } in
  match exact (t (Bvar bid)) st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof complete after exact hyp" true (is_complete st')

(* [exact] fails with a clear message when there are no goals left. *)
let test_exact_no_goals () =
  let st = start (t (Sort 1)) in
  let st' = match exact (t (Sort 0)) st with
    | Success s -> s
    | Failure _ -> Alcotest.fail "first exact should succeed"
  in
  match exact (t (Sort 0)) st' with
  | Failure msg ->
      Alcotest.(check string) "no goals message" "No goals remaining." msg
  | Success _ -> Alcotest.fail "expected Failure on completed state"

(* Ill-typed or unknown terms should come back as [Failure], not escape as exceptions. *)
let test_exact_elab_error () =
  let st = start (t (Sort 0)) in
  match exact (t (Name "no_such_term")) st with
  | Success _ -> Alcotest.fail "expected Failure but got Success"
  | Failure msg ->
      Alcotest.(check bool) "error message is non-empty" true (String.length msg > 0)

let suite =
  let open Alcotest in
  ( "Tactic.exact",
    [
      test_case "closes goal with matching type" `Quick test_exact_sort;
      test_case "fails on type mismatch"         `Quick test_exact_wrong_type;
      test_case "closes goal via hypothesis"     `Quick test_exact_hyp;
      test_case "fails when no goals remain"     `Quick test_exact_no_goals;
      test_case "catches elaboration errors"     `Quick test_exact_elab_error;
    ] )
