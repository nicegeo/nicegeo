open Elab.Term
open Elab.Proofstate
open Automation.Tactics

let e = Elab.Interface.create ()
let t k = { inner = k; loc = dummy_range }
let name s = t (Name s)
let app f x = t (App (f, x))
let eq_term a lhs rhs = app (app (app (name "Eq") a) lhs) rhs
let start ty = init_state ~elab_ctx:e ty

(* [Eq A a a] : both sides are syntactically identical Names. No beta-reduction needed. *)
let test_refl_identical () =
  let a = name "A" in
  let tm = name "a" in
  let st = start (eq_term a tm tm) in
  match reflexivity st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' ->
      Alcotest.(check bool) "proof is complete after reflexivity" true (is_complete st')

(** [Eq A (f x) (f x)] — both sides are the same App node. *)
let test_refl_app () =
  let a = name "A" in
  let side = app (name "f") (name "x") in
  let st = start (eq_term a side side) in
  match reflexivity st with
  | Failure msg -> Alcotest.failf "expected Success: %s" msg
  | Success st' -> Alcotest.(check bool) "proof complete" true (is_complete st')

let suite =
  let open Alcotest in
  ( "Tactic.reflexivity",
    [
      test_case "identical names" `Quick test_refl_identical;
      test_case "identical App nodes" `Quick test_refl_app;
    ] )
