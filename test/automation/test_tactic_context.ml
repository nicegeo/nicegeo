open Elab.Term
open Elab.Types
open Elab.Proofstate
open Automation.Tactics

let t k = { inner = k; loc = dummy_range }
let name s = t (Name s)

let setup_env () =
  let ctx = Elab.Interface.create () in
  Hashtbl.add ctx.env "A" { name = "A"; ty = t (Sort 0); data = Axiom };
  Hashtbl.add ctx.env "B" { name = "B"; ty = t (Sort 0); data = Axiom };
  ctx

let start ctx ty = init_state ~elab_ctx:ctx ty

(** [intro] should peel off the arrow, push the hypothesis into the context, and leave the
    return type as the new goal. *)
let test_intro_success () =
  let ctx = setup_env () in
  let goal_ty = t (Arrow (Some "x", 0, name "A", name "B")) in
  let st = start ctx goal_ty in

  match intro "h_A" st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' -> (
      match st'.open_goals with
      | [ g ] ->
          (* verify the goal type is now just B *)
          Alcotest.(check bool)
            "goal is B"
            true
            (match g.goal_type.inner with Name "B" -> true | _ -> false);
          (* verify the local context has exactly 1 hypothesis *)
          Alcotest.(check int) "context has 1 hypothesis" 1 (List.length g.lctx);
          (* verify the hypothesis is named "h_A" *)
          let hyp = List.hd g.lctx in
          Alcotest.(check string) "hypothesis name" "h_A" (Option.get hyp.name)
      | _ -> Alcotest.fail "expected exactly 1 open goal")

(** [intro] should fail safely if goal is not an implication/forall. *)
let test_intro_failure () =
  let ctx = setup_env () in
  let goal_ty = name "A" in
  let st = start ctx goal_ty in

  match intro "h" st with
  | Success _ -> Alcotest.fail "expected Failure but intro succeeded on a non-arrow goal"
  | Failure _ -> Alcotest.(check pass) "failed safely" () ()

(** [have] should split the current goal G into two goals:
    - The type T
    - The continuation T -> G *)
let test_have_success () =
  let ctx = setup_env () in
  let goal_ty = name "B" in
  let st = start ctx goal_ty in

  match have "h_A" (name "A") st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' -> (
      match st'.open_goals with
      | [ proof_goal; cont_goal ] ->
          (* first goal prove hypothesis A *)
          Alcotest.(check bool)
            "first goal is A"
            true
            (match proof_goal.goal_type.inner with Name "A" -> true | _ -> false);
          (* second goal continuation (h_A : A) -> B *)
          Alcotest.(check bool)
            "second goal is Arrow"
            true
            (match cont_goal.goal_type.inner with Arrow _ -> true | _ -> false)
      | _ ->
          Alcotest.failf
            "expected exactly 2 open goals, got %d"
            (List.length st'.open_goals))

let suite =
  let open Alcotest in
  ( "Tactic.Context",
    [
      test_case "intro peels arrow and updates ctx" `Quick test_intro_success;
      test_case "intro fails on non-arrow" `Quick test_intro_failure;
      test_case "have splits goal into proof and continuation" `Quick test_have_success;
    ] )
