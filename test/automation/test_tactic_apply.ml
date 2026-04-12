open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Tactic
open Automation.Tactics

let e = Elab.Interface.create ()
let t k = { inner = k; loc = dummy_range }

(* Build a goal state with one hypothesis [name : hyp_ty] and goal type [goal_ty]. *)
let start_with_hyp hyp_name hyp_ty goal_ty =
  let bid = gen_binder_id () in
  let st = init_state ~elab_ctx:e (mk_arrow (Some hyp_name) bid hyp_ty goal_ty) in
  match intro hyp_name st with
  | Success st -> st
  | _ -> failwith "intro failed in start_with_hyp"

let bind_names (g : goal) (arg : term) : term =
  List.fold_right
    (fun hyp res ->
      match hyp.name with Some name -> subst res (Name name) (Bvar hyp.bid) | _ -> res)
    g.lctx
    arg

(* [h : Sort 1 -> Sort 0], goal [Sort 0]: apply opens one subgoal [Sort 1]. *)
let test_apply_opens_subgoal () =
  let premise = t (Sort 1) in
  let conclusion = t (Sort 0) in
  let arrow_bid = gen_binder_id () in
  let h_ty = t (Arrow (None, arrow_bid, premise, conclusion)) in
  let st = start_with_hyp "h" h_ty conclusion in
  let tm = bind_names (List.hd st.open_goals) (mk_name "h") in
  print_endline ("tm: " ^ pp_term e tm);
  try
    match apply tm st with
    | Failure msg -> Alcotest.failf "expected Success: %s" msg
    | Success st' ->
        Alcotest.(check int) "one subgoal remaining" 1 (List.length st'.open_goals);
        Alcotest.(check bool)
          "subgoal type is Sort 1"
          true
          (st'.open_goals |> List.hd |> fun g -> g.goal_type.inner = Sort 1)
  with Elab.Error.ElabError err ->
    Alcotest.failf "unexpected elaboration error: %s" (Elab.Error.pp_exn e err)

(* Conclusion does not match goal — apply should fail. *)
let test_apply_conclusion_mismatch () =
  let arrow_bid = gen_binder_id () in
  let h_ty = t (Arrow (None, arrow_bid, t (Sort 1), t (Sort 1))) in
  let st = start_with_hyp "h" h_ty (t (Sort 0)) in
  let tm = bind_names (List.hd st.open_goals) (mk_name "h") in
  match apply tm st with Success _ -> Alcotest.fail "expected Failure" | Failure _ -> ()

(* Unknown name should fail. *)
let test_apply_unknown_name () =
  let st = init_state ~elab_ctx:e (t (Sort 0)) in
  let tm = bind_names (List.hd st.open_goals) (mk_name "no_such_lemma") in
  match apply tm st with Success _ -> Alcotest.fail "expected Failure" | Failure _ -> ()

(* No goals remaining: use the no-arrow path to fully close the state, then apply again. *)
let test_apply_no_goals () =
  let st = { statement = t (Sort 0); open_goals = []; elab_ctx = e } in
  match apply (mk_name "h") st with
  | Failure _ -> ()
  | Success _ -> Alcotest.fail "expected Failure on completed state"

let test_apply_no_args () = 
  let st = start_with_hyp "h" (mk_name "A") (mk_name "A") in
  let tm = bind_names (List.hd st.open_goals) (mk_name "h") in
  match apply tm st with Success st -> (
    Alcotest.(check bool) "proof complete after apply" true (is_complete st)
  ) | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg

let test_multiple_args () = 
  let st = start_with_hyp "h" (Elab.Interface.parse_term "A -> B -> A") (mk_name "A") in
  let tm = bind_names (List.hd st.open_goals) (mk_name "h") in
  match apply tm st with Success st -> (
    Alcotest.(check int) "two subgoals remaining" 2 (List.length st.open_goals);
    match st.open_goals with
    | [ g1; g2 ] ->
        Alcotest.(check bool) "first subgoal is A" true (g1.goal_type.inner = Name "A");
        Alcotest.(check bool) "second subgoal is B" true (g2.goal_type.inner = Name "B")
    | _ -> Alcotest.fail "expected exactly two subgoals"
  ) | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg

let suite =
  let open Alcotest in
  ( "Tactic.apply",
    [
      test_case "opens subgoal for premise" `Quick test_apply_opens_subgoal;
      test_case "fails on conclusion mismatch" `Quick test_apply_conclusion_mismatch;
      test_case "fails on unknown name" `Quick test_apply_unknown_name;
      test_case "fails when no goals remaining" `Quick test_apply_no_goals;
      test_case "test apply works like exact" `Quick test_apply_no_args;
      test_case "test multiple arguments" `Quick test_multiple_args;
    ] )
