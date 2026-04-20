open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic
open Automation.Tactics

(* Copied from test_tactic_exists.ml and modified *)

let path_to_env = "../../../../synthetic/env.ncg"

(*
  Create the starting environment that we use in the tests.
  It adds axioms for the types we care about in the tests.
*)
let make_env () =
  let env = Elab.Interface.create () in
  Elab.Interface.process_file env path_to_env;
  let process s =
    let lexbuf = Sedlexing.Utf8.from_string s in
    let parse = MenhirLib.Convert.Simplified.traditional2revised Elab.Parser.main in
    let stmts = parse (Sedlexing.with_tokenizer Elab.Lexer.token lexbuf) in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  (* Elab.Interface.process_statement adds the processed statements to the
  provided environment, so these adds the declared values to the environment *)
  process "Axiom A : Prop";
  process "Axiom B : Prop";
  process "Axiom a : A";
  process "Axiom b : B";
  (env, process)

let elab (env : Elab.Types.ctx) s =
  (* The elaborate function clears all metavariables from env.metas (since it assumes
  that the metas hash tables is empty to start with), which causes the solutions
  for the holes for previous (solved) goals to disappear, so copy metas here *)
  let metas = Hashtbl.copy env.metas in
  let env = { env with metas } in
  Elab.Typecheck.elaborate env (Elab.Interface.parse_term s) None

let run_tactic tac (st : proof_state) =
  match tac st with
  | Failure msg -> Alcotest.failf "tactic failed: %s" msg
  | Success st' -> st'

(** Check that the kernel accepts [proof] as having type [goal_ty]. *)
let kernel_check env proof goal_ty =
  let proof_k = Elab.Convert.conv_to_kterm (replace_metas env proof) in
  let ty_k = Elab.Convert.conv_to_kterm (replace_metas env goal_ty) in
  try
    Kernel.Interface.add_theorem env.kenv "test" ty_k proof_k;
    Hashtbl.remove env.kenv.types "test";
    true
  with Kernel.Exceptions.TypeError _ -> false

let check_terms_equal (msg : string) (env : Elab.Types.ctx) (actual_term : Elab.Term.term)
    (expected_term : Elab.Term.term) : unit =
  let got = pp_term env (Elab.Reduce.reduce env expected_term) in
  let exp = pp_term env actual_term in
  Alcotest.(check string) msg exp got

(* TODO: test something where unification has to use something from context (especially if it needs to use variable introduced by inner
  function) *)
(* Check that single usage of `exists` creates the correct new goal type. *)
let test_left_simple () =
  let env, _ = make_env () in
  let goal_ty = elab env "Or A B" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic left st in
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  check_terms_equal "new goal is A" env (List.hd st.open_goals).goal_type (elab env "A");

  let st = run_tactic (exact (elab env "a")) st in
  Alcotest.(check int) "no remaining goals" 0 (List.length st.open_goals);

  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty)

(* Check that `exists` can infer the motive properly referencing something in the local
   context *)
let test_exists_lctx () =
  let env, _ = make_env () in
  let goal_ty = elab env "(b : A) -> Exists A (fun (c : A) => b = c)" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (intro "b") st in
  let bid =
    match (List.hd st.open_goals).lctx with
    | [ { name = Some "b"; bid; _ } ] -> bid
    | _ -> Alcotest.fail "expected one hypothesis named b in local context"
  in
  let st = run_tactic (exists (mk_bvar bid)) st in
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  let got =
    Elab.Pretty.term_to_string
      env
      ~lctx:(List.hd st.open_goals).lctx
      (Elab.Reduce.reduce env (List.hd st.open_goals).goal_type)
  in
  let exp = "Eq A b b" in
  Alcotest.(check string) "new goal is b = b" exp got;
  (* close the goal and typecheck because we can *)
  let st = run_tactic reflexivity st in
  Alcotest.(check int) "no remaining goals" 0 (List.length st.open_goals);
  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty);
  ()

let test_exists_unify () =
  let open Elab.Types in
  let env, _ = make_env () in
  let goal_ty =
    elab
      env
      "(B : Type) -> (Q : B -> Prop) -> (b : B) -> (hb : Q b) -> (fun P => Exists B P) Q"
  in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (intros [ "B"; "Q"; "b"; "hb" ]) st in
  let b_entry = List.find (fun h -> h.name = Some "b") (List.hd st.open_goals).lctx in
  let st = run_tactic (exists (mk_bvar b_entry.bid)) st in
  let hb_entry = List.find (fun h -> h.name = Some "hb") (List.hd st.open_goals).lctx in
  let st = run_tactic (exact (mk_bvar hb_entry.bid)) st in
  Alcotest.(check int) "no remaining goals" 0 (List.length st.open_goals);
  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty);
  ()

(*
  Checks that using `exists` and then closing a trivial goal produces
  a proof term that the kernel accepts.
*)
let test_exists_kernel_check () =
  let env, _ = make_env () in
  let goal_ty = elab env "Exists A (fun (a : A) => True)" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (exists (elab env "a")) st in
  let st = run_tactic (exact (mk_name "True.intro")) st in
  Alcotest.(check bool) "no remaining goals" true (is_complete st);
  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty)

let suite =
  let open Alcotest in
  ("Tactic.construct_or", [ test_case "left simple" `Quick test_left_simple ])
