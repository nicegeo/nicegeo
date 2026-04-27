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

let simpterm : Simpterm.term Alcotest.testable =
  Alcotest.testable
    (fun fmt t ->
      Format.fprintf fmt "%s" (Elab.Pretty.term_to_string env (Simpterm.from_simpterm t)))
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

let test_elim_eq_basic () =
  let open Simpterm in
  let a, b, c, d = (Bvar 1, Bvar 2, Bvar 3, Bvar 4) in
  let add t1 t2 = App (App (Name "Add", t1), t2) in
  let ( ++ ) = add in
  let eq t1 t2 = App (App (App (Name "Eq", Name "Measure"), t1), t2) in
  let ( == ) = eq in
  let lt t1 t2 = App (App (Name "Lt", t1), t2) in
  let ( << ) = lt in
  let constrain_terms =
    [ (Bvar 5, a == b ++ c); (Bvar 6, a << d); (Bvar 7, b << a); (Bvar 8, c == d) ]
  in
  let constrains =
    List.map
      (fun (proof, tm) ->
        let c = create_constrain tm proof in
        match c with Some c -> c | None -> Alcotest.fail "create_constrain failed")
      constrain_terms
  in

  let cs = elim_eq constrains 0 (Bvar 1) in
  Alcotest.(check int) "number of remaining constrains" 3 (List.length cs);
  let c1 = List.nth cs 0 in
  let c2 = List.nth cs 1 in
  let c3 = List.nth cs 2 in
  Alcotest.(check simpterm) "c1 atom is replaced" (b ++ c << d) (constrain_ty c1);
  Alcotest.(check simpterm) "c2 atom is replaced" (b << b ++ c) (constrain_ty c2);
  Alcotest.(check simpterm) "c3 unchanged" (c == d) (constrain_ty c3);

  let lctx =
    List.map
      (fun (proof, ty) ->
        Elab.Types.
          {
            bid =
              (match proof with Bvar bid -> bid | _ -> failwith "unexpected proof term");
            name = None;
            ty = from_simpterm ty;
          })
      constrain_terms
    @ List.init 4 (fun i ->
        Elab.Types.
          {
            bid = i + 1;
            name = Some ("x" ^ string_of_int (i + 1));
            ty = Elab.Proofstate.mk_name "Measure";
          })
  in

  List.iter
    (fun c ->
      check (fun () ->
          let proof_ty = Elab.Typecheck.infertype env lctx (from_simpterm c.proof) in
          print_endline ("proof type: " ^ Elab.Pretty.term_to_string env proof_ty);
          Elab.Typecheck.unify
            env
            ~lctx
            proof_ty
            (Hashtbl.create 0)
            (constrain_ty c |> from_simpterm)
            (Hashtbl.create 0)))
    cs;

  ()

let test_elim_eq_more () =
  let open Simpterm in
  let a, b, c, d = (Bvar 1, Bvar 2, Bvar 3, Bvar 4) in
  let add t1 t2 = App (App (Name "Add", t1), t2) in
  let ( ++ ) = add in
  let eq t1 t2 = App (App (App (Name "Eq", Name "Measure"), t1), t2) in
  let ( == ) = eq in
  let lt t1 t2 = App (App (Name "Lt", t1), t2) in
  let ( << ) = lt in
  let constrain_terms =
    [
      (Bvar 5, a ++ a ++ d == b ++ c);
      (Bvar 6, a << d);
      (Bvar 7, b ++ b ++ d == a ++ a ++ a ++ c ++ c);
      (Bvar 8, a ++ a ++ d == b ++ c);
      (Bvar 9, b ++ d << a ++ a);
    ]
  in
  (* original: 2a + d = b + c; a < d; 2b + d = 3a + 2c; 2a + d = b + c *)
  (* cancelling a: 
  b + c < 3d;
  6a + 3d = 3b + 3c and 4b + 2d = 6a + 4c -> 6a + 4c + 3d = 3b + 3c + 4c and 4b + 5d = 6a + 4c + 3d -> 4b + 5d = 3b + 7c
  b + c = b + c
  b + 2d < b + c
   *)
  let constrains =
    List.map
      (fun (proof, tm) ->
        let c = create_constrain tm proof in
        match c with Some c -> c | None -> Alcotest.fail "create_constrain failed")
      constrain_terms
  in

  let cs = elim_eq constrains 0 (Bvar 1) in
  Alcotest.(check int) "number of remaining constrains" 4 (List.length cs);
  let c1 = List.nth cs 0 in
  let c2 = List.nth cs 1 in
  let c3 = List.nth cs 2 in
  let c4 = List.nth cs 3 in
  (* print_endline ("c1: " ^ Elab.Pretty.term_to_string env (from_simpterm (constrain_ty c1)));
  print_endline ("c2: " ^ Elab.Pretty.term_to_string env (from_simpterm (constrain_ty c2)));
  print_endline ("c3: " ^ Elab.Pretty.term_to_string env (from_simpterm (constrain_ty c3)));
  print_endline ("c4: " ^ Elab.Pretty.term_to_string env (from_simpterm (constrain_ty c4))); *)

  Alcotest.(check simpterm) "c1 correct" (b ++ c << d ++ d ++ d) (constrain_ty c1);
  Alcotest.(check simpterm)
    "c2 correct"
    (b ++ b ++ b ++ b ++ d ++ d ++ d ++ d ++ d
    == b ++ b ++ b ++ c ++ c ++ c ++ c ++ c ++ c ++ c)
    (constrain_ty c2);
  Alcotest.(check simpterm) "c3 correct" (b ++ c == b ++ c) (constrain_ty c3);
  Alcotest.(check simpterm) "c4 correct" (b ++ d ++ d << b ++ c) (constrain_ty c4);
  let lctx =
    List.map
      (fun (proof, ty) ->
        Elab.Types.
          {
            bid =
              (match proof with Bvar bid -> bid | _ -> failwith "unexpected proof term");
            name = None;
            ty = from_simpterm ty;
          })
      constrain_terms
    @ List.init 4 (fun i ->
        Elab.Types.
          {
            bid = i + 1;
            name = Some ("x" ^ string_of_int (i + 1));
            ty = Elab.Proofstate.mk_name "Measure";
          })
  in

  List.iter
    (fun c ->
      print_endline ("proof: " ^ Elab.Pretty.term_to_string env (from_simpterm c.proof));
      check (fun () ->
          let proof_ty = Elab.Typecheck.infertype env lctx (from_simpterm c.proof) in
          print_endline ("proof type: " ^ Elab.Pretty.term_to_string env proof_ty);
          Elab.Typecheck.unify
            env
            ~lctx
            proof_ty
            (Hashtbl.create 0)
            (constrain_ty c |> from_simpterm)
            (Hashtbl.create 0)))
    cs;

  ()

let suite =
  let open Alcotest in
  ( "fm_elim",
    [
      test_case "to_constrain basic" `Quick test_to_constrain_basic;
      test_case "elim_eq basic" `Quick test_elim_eq_basic;
      test_case "elim_eq more" `Quick test_elim_eq_more;
    ] )
