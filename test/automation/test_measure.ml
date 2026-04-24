open Automation.Measure

let sctx = Elab.Interface.create ()

let summand : summand Alcotest.testable =
  Alcotest.testable
    (fun fmt t ->
      Format.fprintf fmt "%s" (Elab.Pretty.term_to_string sctx (summand_to_term t)))
    (fun t1 t2 -> t1 = t2)

let test_to_summand_basic () =
  let open Elab.Proofstate in
  (* mk_[termkind] helpers *)
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
  let sorted_summands = List.sort (fun s1 s2 -> compare (order s1) (order s2)) summands in
  Alcotest.(check (list summand)) "summands are sorted by order" sorted_summands summands

let suite =
  let open Alcotest in
    ( "measure",
      [
        test_case "to_summand basic" `Quick test_to_summand_basic;
        test_case "summand order" `Quick test_summand_order;
      ] );
