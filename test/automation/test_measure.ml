open Automation
open Measure

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

let test_to_summand_basic () =
  (* mk_[termkind] helpers *)
  let open Elab.Proofstate in
  let t = mk_app (mk_app (mk_name "Length") (mk_bvar 1)) (mk_bvar 2) in
  let expected = Length (1, 2) in
  Alcotest.(check (option summand)) "length _1 _2" (to_summand t) (Some expected);

  let t =
    mk_app (mk_app (mk_app (mk_name "Angle") (mk_bvar 3)) (mk_bvar 4)) (mk_bvar 5)
  in
  let expected = Angle (3, 4, 5) in
  Alcotest.(check (option summand)) "angle _3 _4 _5" (to_summand t) (Some expected);

  let t = mk_app (mk_app (mk_app (mk_name "Area") (mk_bvar 6)) (mk_bvar 7)) (mk_bvar 8) in
  let expected = Area (6, 7, 8) in
  Alcotest.(check (option summand)) "area _6 _7 _8" (to_summand t) (Some expected);

  let t = mk_name "Zero" in
  let expected = Zero in
  Alcotest.(check (option summand)) "Zero" (to_summand t) (Some expected);

  let t = mk_name "RightAngle" in
  let expected = RightAngle in
  Alcotest.(check (option summand)) "RightAngle" (to_summand t) (Some expected);

  let t = mk_bvar 9 in
  let expected = Bvar 9 in
  Alcotest.(check (option summand)) "Bvar 9" (to_summand t) (Some expected);

  let t = mk_name "NotASummand" in
  Alcotest.(check (option summand)) "NotASummand" (to_summand t) None;

  let t =
    mk_fun None (Elab.Term.gen_binder_id ()) (mk_name "SomeType") (mk_name "NotASummand")
  in
  Alcotest.(check (option summand)) "function is not a summand" (to_summand t) None;

  ()

let test_summand_order () =
  let zero = Zero in
  let rightangle = RightAngle in
  let l1 = Length (1, 2) in
  let l2 = Length (1, 3) in
  let l3 = Length (2, 2) in
  let ang1 = Angle (3, 4, 5) in
  let ang2 = Angle (3, 4, 6) in
  let ang3 = Angle (3, 5, 5) in
  let ang4 = Angle (4, 4, 5) in
  let area1 = Area (6, 7, 8) in
  let area2 = Area (6, 7, 9) in
  let b1 = Bvar 1 in
  let b2 = Bvar 2 in

  let summands =
    [ zero; rightangle; l1; l2; l3; ang1; ang2; ang3; ang4; area1; area2; b1; b2 ]
  in
  let sorted_summands = List.sort compare summands in
  Alcotest.(check (list summand)) "summands are sorted by order" sorted_summands summands

(** Check that the kernel accepts [proof] as having type [goal_ty]. *)
let kernel_check env proof goal_ty =
  let open Elab.Typecheck in
  let proof_k = Elab.Convert.conv_to_kterm (replace_metas env proof) in
  let ty_k = Elab.Convert.conv_to_kterm (replace_metas env goal_ty) in
  try
    Kernel.Interface.add_theorem env.kenv "test" ty_k proof_k;
    Hashtbl.remove env.kenv.types "test";
    true
  with Kernel.Exceptions.TypeError _ -> false

let test_to_measure () =
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
    Bvar 1 ++ (Bvar 2 ++ Bvar 3)
    ++ (Bvar 4 ++ (Bvar 5 ++ Bvar 6 ++ (Bvar 7 ++ (Bvar 8 ++ Bvar 9))))
  in
  let tm_normal_exp =
    Bvar 1 ++ Bvar 2 ++ Bvar 3 ++ Bvar 4 ++ Bvar 5 ++ Bvar 6 ++ Bvar 7 ++ Bvar 8 ++ Bvar 9
  in
  let m = to_measure tm in
  let m = match m with Some m -> m | None -> Alcotest.fail "to_measure failed" in
  let tm_normal_got = to_simpterm (measure_to_term m) in
  Alcotest.(check simpterm)
    "measure_to_term . to_measure = id"
    tm_normal_exp
    tm_normal_got;
  Alcotest.(check simpterm) "original is unchanged" tm m.original;

  (* check the proof type (in elab) *)
  let open Elab.Types in
  let lctx =
    List.init 9 (fun i ->
        {
          bid = i + 1;
          name = Some ("x" ^ string_of_int (i + 1));
          ty = Elab.Proofstate.mk_name "Measure";
        })
  in
  print_endline ("proof: " ^ Elab.Pretty.term_to_string env (from_simpterm m.proof));
  let proof_ty = Elab.Typecheck.infertype env lctx (Simpterm.from_simpterm m.proof) in
  let expected_proof_ty =
    from_simpterm (apps (Name "Eq") [ Name "Measure"; tm_normal_got; tm ])
  in
  Elab.Typecheck.unify
    env
    ~lctx
    proof_ty
    (Hashtbl.create 0)
    expected_proof_ty
    (Hashtbl.create 0);

  ()

let check f =
  try f ()
  with Elab.Error.ElabError info ->
    Alcotest.failf "unexpected elaboration error: %s" (Elab.Error.pp_exn env info)

let test_sort () =
  let open Simpterm in
  let add t1 t2 = App (App (Name "Add", t1), t2) in
  let ( ++ ) = add in
  let tm = Bvar 6 ++ Bvar 3 ++ (Bvar 4 ++ (Bvar 7 ++ Bvar 5) ++ Bvar 1) ++ Bvar 2 in
  let tm_normal_exp =
    Bvar 1 ++ Bvar 2 ++ Bvar 3 ++ Bvar 4 ++ Bvar 5 ++ Bvar 6 ++ Bvar 7
  in
  let m = to_measure tm in
  let m = match m with Some m -> m | None -> Alcotest.fail "to_measure failed" in
  let m = sort m in
  let tm_normal_got = to_simpterm (measure_to_term m) in
  Alcotest.(check simpterm) "sort measure" tm_normal_exp tm_normal_got;

  (* check the proof type (in elab) *)
  let open Elab.Types in
  let lctx =
    List.init 9 (fun i ->
        {
          bid = i + 1;
          name = Some ("x" ^ string_of_int (i + 1));
          ty = Elab.Proofstate.mk_name "Measure";
        })
  in
  print_endline ("proof: " ^ Elab.Pretty.term_to_string env (from_simpterm m.proof));
  let proof_ty =
    check (fun () -> Elab.Typecheck.infertype env lctx (Simpterm.from_simpterm m.proof))
  in
  let expected_proof_ty =
    from_simpterm (apps (Name "Eq") [ Name "Measure"; tm_normal_got; tm ])
  in
  Elab.Typecheck.unify
    env
    ~lctx
    proof_ty
    (Hashtbl.create 0)
    expected_proof_ty
    (Hashtbl.create 0);
  ()

let suite =
  let open Alcotest in
  ( "measure",
    [
      test_case "to_summand basic" `Quick test_to_summand_basic;
      test_case "summand order" `Quick test_summand_order;
      test_case "to_measure" `Quick test_to_measure;
      test_case "sort" `Quick test_sort;
    ] )
