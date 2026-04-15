open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic
open Automation.Tactics

let path_to_env = "../../../../synthetic/env.ncg"
let name s = mk_name s

let make_env () =
  let env = Elab.Interface.create () in
  Elab.Interface.process_file env path_to_env;
  let process s =
    let lexbuf = Sedlexing.Utf8.from_string s in
    let parse = MenhirLib.Convert.Simplified.traditional2revised Elab.Parser.main in
    let stmts = parse (Sedlexing.with_tokenizer Elab.Lexer.token lexbuf) in
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

let to_kterm _env tm = Elab.Convert.conv_to_kterm tm

let kernel_check env proof goal_ty =
  let proof_k = to_kterm env (replace_metas env proof) in
  let ty_k = to_kterm env (replace_metas env goal_ty) in
  try
    Kernel.Interface.add_theorem env.kenv "test" ty_k proof_k;
    Hashtbl.remove env.kenv.types "test";
    true
  with Kernel.Exceptions.TypeError _ -> false

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
          Alcotest.failf
            "expected exactly 2 open goals, got %d"
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
  let hyp = { bid; name = Some "h"; ty = name "A" } in
  let goal_ty = elab env "And A B" in
  let id = gen_hole_id () in
  Hashtbl.replace env.metas id { ty = Some goal_ty; context = [ bid ]; sol = None };
  let g = { lctx = [ hyp ]; goal_type = goal_ty; goal_id = id } in
  let st = { statement = mk_hole id; open_goals = [ g ]; elab_ctx = env } in

  match split st with
  | Failure msg -> Alcotest.failf "expected Success but got Failure: %s" msg
  | Success st' ->
      List.iter
        (fun g ->
          Alcotest.(check int) "subgoal inherits context" 1 (List.length g.lctx);
          Alcotest.(check string)
            "hypothesis name"
            "h"
            (match (List.hd g.lctx).name with Some n -> n | None -> ""))
        st'.open_goals

let test_split_kernel_check () =
  let env = make_env () in
  let process s =
    let lexbuf = Sedlexing.Utf8.from_string s in
    let parse = MenhirLib.Convert.Simplified.traditional2revised Elab.Parser.main in
    let stmts = parse (Sedlexing.with_tokenizer Elab.Lexer.token lexbuf) in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  process "Axiom a_proof : A";
  process "Axiom b_proof : B";
  let goal_ty = elab env "And A B" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st =
    st |> run_tactic split
    |> run_tactic (exact (name "a_proof"))
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
