open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Tactics

let path_to_env = "../../../../synthetic/env.ncg"

let t k = { inner = k; loc = dummy_range }
let name s = t (Name s)

let make_env () =
  let env = Elab.Interface.create_with_env_path path_to_env in
  let process s =
    let lexbuf = Lexing.from_string s in
    let stmts = Elab.Parser.main Elab.Lexer.token lexbuf in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  process "Axiom A : Prop";
  process "Axiom B : Prop";
  env

let elab env s = Elab.Typecheck.elaborate env (Elab.Interface.parse_term s) None

let run_tactic tac st =
  match tac st with
  | Failure msg -> Alcotest.failf "tactic failed: %s" msg
  | Success st' -> st'

let to_kterm env tm =
  Elab.Reduce.delta_reduce env tm true
  |> Elab.Reduce.reduce env |> Elab.Convert.conv_to_kterm

let kernel_check env proof goal_ty =
  let proof_k = to_kterm env (apply_meta env proof) in
  let ty_k = to_kterm env goal_ty in
  let inferred = Kernel.Infer.inferType env.kenv (Hashtbl.create 0) proof_k in
  Kernel.Infer.isDefEq env.kenv (Hashtbl.create 0) inferred ty_k

let test_split_success () =
  let env = make_env () in
  let goal_ty = elab env "And A B" in
  let st = init_state ~elab_ctx:env goal_ty in

  match split st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' -> (
      match st'.open_goals with
      | [ g_a; g_b ] ->
          Alcotest.(check bool)
            "first subgoal is A"
            true
            (match g_a.goal_type.inner with Name "A" -> true | _ -> false);
          Alcotest.(check bool)
            "second subgoal is B"
            true
            (match g_b.goal_type.inner with Name "B" -> true | _ -> false)
      | _ ->
          Alcotest.failf "expected exactly 2 open goals, got %d"
            (List.length st'.open_goals))

let test_split_failure_non_and () =
  let env = make_env () in
  let goal_ty = elab env "A" in
  let st = init_state ~elab_ctx:env goal_ty in

  match split st with
  | Success _ -> Alcotest.fail "expected Failure but split succeeded on a non-And goal"
  | Failure _ -> Alcotest.(check pass) "failed safely" () ()

let test_split_no_goals () =
  let env = make_env () in
  let goal_ty = elab env "A" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st' =
    match sorry st with
    | Success s -> s
    | Failure _ -> Alcotest.fail "sorry should succeed"
  in
  match split st' with
  | Success _ -> Alcotest.fail "expected Failure on completed state"
  | Failure msg -> Alcotest.(check string) "no goals message" "No goals remaining." msg

let test_split_preserves_ctx () =
  let env = make_env () in
  let bid = gen_binder_id () in
  let hyp = { hyp_name = "h"; hyp_bid = bid; hyp_def = None; hyp_type = name "A" } in
  let goal_ty = elab env "And A B" in
  let id = gen_hole_id () in
  Hashtbl.replace env.metas id { ty = Some goal_ty; context = [ bid ]; sol = None };
  let g = { ctx = [ hyp ]; goal_type = goal_ty; goal_id = id } in
  let st = { statement = t (Hole id); open_goals = [ g ]; elab_ctx = env } in

  match split st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' ->
      List.iter
        (fun g ->
          Alcotest.(check int) "subgoal inherits context" 1 (List.length g.ctx);
          Alcotest.(check string) "hypothesis name" "h" (List.hd g.ctx).hyp_name)
        st'.open_goals

let test_split_kernel_check () =
  let env = make_env () in
  let process s =
    let lexbuf = Lexing.from_string s in
    let stmts = Elab.Parser.main Elab.Lexer.token lexbuf in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  process "Axiom a_proof : A";
  process "Axiom b_proof : B";
  let goal_ty = elab env "And A B" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st =
    st |> run_tactic split |> run_tactic (exact (name "a_proof"))
    |> run_tactic (exact (name "b_proof"))
  in
  Alcotest.(check bool) "no remaining goals" true (is_complete st);
  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty)

let suite =
  let open Alcotest in
  ( "Tactic.split",
    [
      test_case "splits And A B into two subgoals" `Quick test_split_success;
      test_case "fails on non-And goal" `Quick test_split_failure_non_and;
      test_case "fails when no goals remain" `Quick test_split_no_goals;
      test_case "subgoals inherit local context" `Quick test_split_preserves_ctx;
      test_case "split kernel check" `Quick test_split_kernel_check;
    ] )
