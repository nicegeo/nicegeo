open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic
open Automation.Tactics

(*
 * This is still based heavily on the rewrite tactic tests, including by copying
 * several of the utility functions. We should still refactor this common 
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
    let lexbuf = Sedlexing.Utf8.from_string s in
    let parse = MenhirLib.Convert.Simplified.traditional2revised Elab.Parser.main in
    let stmts = parse (Sedlexing.with_tokenizer Elab.Lexer.token lexbuf) in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  process "Axiom A : Type";
  process "Axiom E : Exists A (fun (a : A) => True)";
  process "Axiom B : Prop";
  (env, process)

let elab env s = Elab.Typecheck.elaborate env (Elab.Interface.parse_term s) None

let run_tactic tac st =
  match tac st with
  | Failure msg -> Alcotest.failf "tactic failed: %s" msg
  | Success st' -> st'

(** Convert an elab term to a kernel term *)
let to_kterm env tm =
  Elab.Reduce.delta_reduce env tm |> Elab.Reduce.reduce env |> Elab.Convert.conv_to_kterm

(** Check that the kernel accepts [proof] as having type [goal_ty]. *)
let kernel_check env proof goal_ty =
  Printf.printf "%s\n" (pp_term env (replace_metas env proof));
  Printf.printf "%s\n" (pp_term env goal_ty);
  let proof_k = to_kterm env (replace_metas env proof) in
  let ty_k = to_kterm env (replace_metas env goal_ty) in
  try
    Kernel.Interface.add_theorem env.kenv "test" ty_k proof_k;
    Hashtbl.remove env.kenv.types "test";
    true
  with Kernel.Exceptions.TypeError _ -> false

(** Test for a simple usage of "choose" using just the global context *)
let test_choose_global () =
  let env, _ = make_env () in
  let st = init_state ~elab_ctx:env (elab env "Exists A (fun (a : A) => True)") in
  let st = run_tactic (choose (elab env "E")) st in
  (* check that the goal is the same as before *)
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  let goal = List.hd st.open_goals in
  let got = pp_term env (Elab.Reduce.reduce env goal.goal_type) in
  let exp = "Exists A (fun (a : A) => True)" in
  Alcotest.(check string) "new goal is still (Exists A (fun (a : A) => True))" exp got;
  (* check for the newly added hypotheses *)
  match goal.lctx with
  | [ ha; a ] ->
      let a_typ = pp_term env a.ty in
      let h = pp_term env (Elab.Reduce.reduce env ha.ty) in
      let exp = "A" in
      Alcotest.(check string) "first hypothesis has type A" a_typ exp;
      let exp = "True" in
      Alcotest.(check string) "second hypothesis has type True" exp h;
      (* finish the proof and do a kernel term check *)
      let st = run_tactic (exists (mk_bvar a.bid)) st in
      let st = run_tactic (exact (mk_name "True.intro")) st in
      Alcotest.(check bool) "no remaining goals" true (is_complete st);
      Alcotest.(check bool)
        "kernel accepts proof"
        true
        (kernel_check st.elab_ctx st.statement goal.goal_type)
  | _ -> Alcotest.fail "expected two hypotheses in the local context"

(** Test for a usage of choose that uses local context *)
let test_choose_local () =
  let env, _ = make_env () in
  let goal_ty = elab env "(e : Exists A (fun (a : A) => B)) -> B" in
  let st = init_state ~elab_ctx:env goal_ty in
  let st = run_tactic (intro "e") st in
  let bid =
    match (List.hd st.open_goals).lctx with
    | [ { name = Some "e"; bid; _ } ] -> bid
    | _ -> Alcotest.fail "expected one hypothesis named b in local context"
  in
  let st = run_tactic (choose (mk_bvar bid)) st in
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  let goal = List.hd st.open_goals in
  let got =
    Elab.Pretty.term_to_string
      env
      ~lctx:(List.hd st.open_goals).lctx
      (Elab.Reduce.reduce env goal.goal_type)
  in
  (* check for the right goal *)
  let exp = "B" in
  Alcotest.(check string) "new goal is B" exp got;
  (* check hypotheses *)
  match goal.lctx with
  | [ ha; a; e ] ->
      let a_typ = pp_term env a.ty in
      let h = pp_term env (Elab.Reduce.reduce env ha.ty) in
      let exp = "A" in
      Alcotest.(check string) "first new hypothesis has type A" a_typ exp;
      let exp = "B" in
      Alcotest.(check string) "second new hypothesis has type B" exp h;
      let exp = "Exists A (fun (a : A) => B)" in
      Alcotest.(check string)
        "old hypothesis still has the right type"
        exp
        (pp_term env e.ty);
      (* finish the proof and do a kernel term check *)
      let st = run_tactic (exact (mk_bvar ha.bid)) st in
      Alcotest.(check bool) "no remaining goals" true (is_complete st);
      Alcotest.(check bool)
        "kernel accepts proof"
        true
        (kernel_check st.elab_ctx st.statement goal_ty)
  | _ -> Alcotest.fail "expected three hypotheses in the local context"

let suite =
  let open Alcotest in
  ( "Tactic.choose",
    [
      test_case "choose global context" `Quick test_choose_global;
      test_case "choose local context" `Quick test_choose_local;
    ] )
