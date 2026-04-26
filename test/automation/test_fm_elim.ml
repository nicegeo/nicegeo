open Automation
open Measure
open Fm_elim

let env = Elab.Interface.create ()

let summand : summand Alcotest.testable =
  Alcotest.testable
    (fun fmt t ->
      Format.fprintf
        fmt
        "%s"
        (Elab.Pretty.term_to_string env (Simpterm.from_simpterm (summand_to_term t))))
    (fun t1 t2 -> t1 = t2)

let check f =
  try f ()
  with Elab.Error.ElabError info ->
    Alcotest.failf "unexpected elaboration error: %s" (Elab.Error.pp_exn env info)

let test_to_constrain_basic () =
  (try Elab.Interface.process_file env "env.ncg"
   with Elab.Error.ElabError info ->
     print_endline
       ("Internal error while processing env.ncg: " ^ Elab.Error.pp_exn env info);
     exit 255);
  (try Elab.Interface.process_file env "tests.ncg"
   with Elab.Error.ElabError info ->
     print_endline ("Error processing tests.ncg:\n" ^ Elab.Error.pp_exn env info);
     exit 255);
  let open Simpterm in
  let add t1 t2 = App (App (Name "Add", t1), t2) in
  let ( ++ ) = add in
  let tm =
    apps
      (App (Name "Eq", Name "Measure"))
      [ Bvar 1 ++ Bvar 4; Bvar 2 ++ (Bvar 4 ++ Bvar 3) ]
  in
  let proof = Bvar 5 in
  (* hypothetically *)
  let c = create_constrain tm proof in
  let c = match c with Some c -> c | None -> Alcotest.fail "create_constrain failed" in
  Alcotest.(check bool) "relation is correct" true (c.r = Eq);
  Alcotest.(check (list summand)) "lhs is correct" [ Bvar 1; Bvar 4 ] c.lhs;
  Alcotest.(check (list summand)) "rhs is correct" [ Bvar 2; Bvar 3; Bvar 4 ] c.rhs;
  let lctx =
    Elab.Types.{ bid = 5; name = None; ty = from_simpterm tm }
    :: List.init 4 (fun i ->
        Elab.Types.
          {
            bid = i + 1;
            name = Some ("x" ^ string_of_int (i + 1));
            ty = Elab.Proofstate.mk_name "Measure";
          })
  in
  print_endline ("proof: " ^ Elab.Pretty.term_to_string env (from_simpterm c.proof));
  let proof_ty =
    check (fun () -> Elab.Typecheck.infertype env lctx (from_simpterm c.proof))
  in
  print_endline ("proof type: " ^ Elab.Pretty.term_to_string env proof_ty);
  let expected_proof_ty =
    from_simpterm
      (apps (Name "Eq") [ Name "Measure"; Bvar 1 ++ Bvar 4; Bvar 2 ++ Bvar 3 ++ Bvar 4 ])
  in
  check (fun () ->
      Elab.Typecheck.unify
        env
        ~lctx
        proof_ty
        (Hashtbl.create 0)
        expected_proof_ty
        (Hashtbl.create 0));

  let c = simp_constrain c in
  Alcotest.(check (list summand)) "lhs is simplified" [ Bvar 1 ] c.lhs;
  Alcotest.(check (list summand)) "rhs is simplified" [ Bvar 2; Bvar 3 ] c.rhs;
  print_endline ("proof: " ^ Elab.Pretty.term_to_string env (from_simpterm c.proof));
  let proof_ty =
    check (fun () -> Elab.Typecheck.infertype env lctx (from_simpterm c.proof))
  in
  print_endline ("proof type: " ^ Elab.Pretty.term_to_string env proof_ty);
  let expected_proof_ty =
    from_simpterm (apps (Name "Eq") [ Name "Measure"; Bvar 1; Bvar 2 ++ Bvar 3 ])
  in
  check (fun () ->
      Elab.Typecheck.unify
        env
        ~lctx
        proof_ty
        (Hashtbl.create 0)
        expected_proof_ty
        (Hashtbl.create 0));

  ()

let suite =
  let open Alcotest in
  ("fm_elim", [ test_case "to_constrain basic" `Quick test_to_constrain_basic ])
