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
    let lexbuf = Lexing.from_string s in
    let stmts = Elab.Parser.main Elab.Lexer.token lexbuf in
    List.iter (Elab.Interface.process_statement env) stmts
  in
  process "Axiom A : Type";
  process "Axiom E : Exists A (fun (a : A) => True)";
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
  Printf.printf "%s\n" (pp_term env proof);
  Printf.printf "%s\n" (pp_term env (replace_metas env proof));
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
  let st = init_state ~elab_ctx:env (elab env "A") in
  let st = run_tactic (choose (elab env "E")) st in
  (* check that the goal is the same as before *)
  Alcotest.(check int) "one remaining goal" 1 (List.length st.open_goals);
  let goal = List.hd st.open_goals in
  let got = pp_term env (Elab.Reduce.reduce env goal.goal_type) in
  let exp = pp_term env (elab env "A") in
  Alcotest.(check string) "new goal is still A" exp got;
  (* check for the newly added hypotheses *)
  match goal.lctx with
  | [hyp_1; hyp_2] ->
      let a_typ = pp_term env hyp_1.ty in
      let h = pp_term env (Elab.Reduce.reduce env hyp_2.ty) in
      Alcotest.(check string) "first hypothesis has type A" exp a_typ;
      let exp = pp_term env (elab env "True") in
      Alcotest.(check string) "second hypothesis has type True" exp h;
      (* finish the proof and do a kernel term check *)
      let st = run_tactic (exact (mk_bvar hyp_1.bid)) st in (* TODO fails *)
      Alcotest.(check bool) "no remaining goals" true (is_complete st);
      Alcotest.(check bool)
        "kernel accepts proof"
        true
        (kernel_check env st.statement goal.goal_type)
  | _ -> Alcotest.fail "expected two hypotheses in the local context"

(* TODO the above, but apply the hypothesis *)

(* Check that `exists` can infer the motive properly referencing something in the local
   context *)
    (*
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
    (kernel_check env st.statement goal_ty)*)

let suite =
  let open Alcotest in
  ( "Tactic.choose",
    [
      test_case "choose global context" `Quick test_choose_global;
      (*test_case "choose unifies with local context" `Quick test_choose_local;*)
    ] )
