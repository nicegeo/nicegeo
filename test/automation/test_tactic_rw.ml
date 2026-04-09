open Elab.Proofstate
open Elab.Tactic
open Automation.Tactics

let path_to_env = "../../../../synthetic/env.ncg"

(*
  Create the starting environment that we use in the tests.
  It adds axioms for the types we care about in the tests.
*)
let make_env () =
  let env = Elab.Interface.create () in
  Elab.Interface.process_file env path_to_env;
  let process s =
    let lexbuf = Lexing.from_string s in
    let stmts = Elab.Parser.main Elab.Lexer.token lexbuf in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  process
    "Theorem Eq.symm : (A: Type) -> (a: A) -> (b: A) -> (Eq A a b) -> (Eq A b a) := fun \
     (A: Type) (a b : A) (eq_ab : Eq A a b) => Eq.elim A a (fun (x : A) => Eq A x a) \
     (Eq.intro A a) b eq_ab";
  process "Axiom A : Type";
  process "Axiom a : A";
  process "Axiom b : A";
  process "Axiom f : A -> A";
  process "Axiom a_eq_b : Eq A a b";
  (env, process)

let elab env s = Elab.Typecheck.elaborate env (Elab.Interface.parse_term s) None

let run_tactic tac st =
  match tac st with
  | Failure msg -> Alcotest.failf "tactic failed: %s" msg
  | Success st' -> st'

(** Convert an elab term to a kernel term *)
let to_kterm env tm =
  Elab.Reduce.delta_reduce env tm true
  |> Elab.Reduce.reduce env |> Elab.Convert.conv_to_kterm

(** Check that the kernel accepts [proof] as having type [goal_ty]. *)
let kernel_check env proof goal_ty =
  let proof_k = to_kterm env (apply_meta env proof) in
  let ty_k = to_kterm env goal_ty in
  let inferred = Kernel.Infer.Internals.inferType env.kenv (Hashtbl.create 0) proof_k in
  Kernel.Infer.Internals.isDefEq env.kenv (Hashtbl.create 0) inferred ty_k

(* Check that single usage of `rewrite` wcreates the correct new goal type. *)
let test_rewrite_simple () =
  let env, _ = make_env () in
  let goal_ty = elab env "Eq A (f a) (f b)" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (rewrite (elab env "a_eq_b")) st in
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  let got = pp_term env (Elab.Reduce.reduce env (List.hd st.open_goals).goal_type) in
  let exp = pp_term env (elab env "Eq A (f b) (f b)") in
  Alcotest.(check string) "new goal is Eq A (f b) (f b)" exp got

(* Check that `rewrite` fails when the `lhs` does not appear. *)
let test_rewrite_no_match () =
  let env, process = make_env () in
  process "Axiom x : A";
  process "Axiom y : A";
  process "Axiom c : A";
  process "Axiom d : A";
  process "Axiom c_eq_d : Eq A c d";
  let st = init_state ~elab_ctx:env (elab env "Eq A x y") in
  match rewrite (elab env "c_eq_d") st with
  | Success _ -> Alcotest.fail "expected missing lhs to fail"
  | Failure _ -> ()

(*
  Checks that using `rewrite` and then `reflexivity` tactics produce
  a proof term that the kernel accepts.
*)
let test_rewrite_kernel_check () =
  let env, _ = make_env () in
  let goal_ty = elab env "Eq A (f a) (f b)" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = st |> run_tactic (rewrite (elab env "a_eq_b")) |> run_tactic reflexivity in
  Alcotest.(check bool) "no remaining goals" true (is_complete st);
  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty)

let suite =
  let open Alcotest in
  ( "Tactic.rewrite",
    [
      test_case "rewrite simple" `Quick test_rewrite_simple;
      test_case "rewrite no match" `Quick test_rewrite_no_match;
      test_case "rewrite kernel check" `Quick test_rewrite_kernel_check;
    ] )
