open Elab.Tactics
open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic

(*
 * This is based heavily on the rewrite tactic tests, including by copying
 * several of the utility functions. We should refactor this common 
 * infrastructure at some point, but for now I want to make sure we can get
 * this tactic out to the library team for use.
 *)

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
  process "Axiom A : Type";
  process "Axiom a : A";
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
  let proof_k = to_kterm env (replace_metas env proof) in
  let ty_k = to_kterm env (replace_metas env goal_ty) in
  let inferred = Kernel.Infer.Internals.inferType env.kenv (Hashtbl.create 0) proof_k in
  Kernel.Infer.Internals.isDefEq env.kenv (Hashtbl.create 0) inferred ty_k

(* Check that single usage of `exists` creates the correct new goal type. *)
let test_exists_simple () =
  let env, _ = make_env () in
  let goal_ty = elab env "Exists A (fun (a : A) => True)" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (exists (elab env "a")) st in
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  let got = pp_term env (Elab.Reduce.reduce env (List.hd st.open_goals).goal_type) in
  let exp = pp_term env (elab env "True") in
  Alcotest.(check string) "new goal is True" exp got

(*
  Checks that using `exists` and then closing a trivial goal produces
  a proof term that the kernel accepts.
*)
let test_exists_kernel_check () =
  let env, _ = make_env () in
  let goal_ty = elab env "Exists A (fun (a : A) => True)" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (exists (elab env "a")) st in
  let st = run_tactic (apply "True.intro") st in
  Alcotest.(check bool) "no remaining goals" true (is_complete st);
  Alcotest.(check bool)
    "kernel accepts proof"
    true
    (kernel_check env st.statement goal_ty)

let suite =
  let open Alcotest in
  ( "Tactic.exists",
    [
      test_case "exists simple" `Quick test_exists_simple;
      test_case "exists kernel check" `Quick test_exists_kernel_check;
    ] )
