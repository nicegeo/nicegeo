open Elab

let () = Automation.Tactics.register ()

let process_ncg contents =
  let path, oc = Filename.open_temp_file "nicegeo-sorry-" ".ncg" in
  output_string oc contents;
  close_out oc;
  Fun.protect
    ~finally:(fun () -> try Sys.remove path with Sys_error _ -> ())
    (fun () -> Interface.process_file (Interface.create ()) path)

(* Proof: Axiom P, prove P using sorry, end with Admitted. — should succeed. *)
let test_sorry_admitted_accepted () =
  process_ncg "Axiom P : Prop\nTheorem t : P\nProof.\n  sorry.\nAdmitted.\n"

(* Proof: Axiom P, prove P using sorry, end with Qed. — should be rejected. *)
let test_sorry_qed_rejected () =
  Alcotest.match_raises
    "sorry with Qed. raises SorryRequiresAdmitted"
    (function
      | Error.ElabError { error_type = Error.SorryRequiresAdmitted; _ } -> true
      | _ -> false)
    (fun () ->
      process_ncg "Axiom P : Prop\nTheorem t : P\nProof.\n  sorry.\nQed.\n")

(* Proof: admitted theorem used as a lemma, closed with Qed. — transitive sorry should be rejected. *)
let test_transitive_sorry_qed_rejected () =
  Alcotest.match_raises
    "transitive sorry with Qed. raises SorryRequiresAdmitted"
    (function
      | Error.ElabError { error_type = Error.SorryRequiresAdmitted; _ } -> true
      | _ -> false)
    (fun () ->
      process_ncg
        "Axiom P : Prop\n\
         Theorem lemma : P\nProof.\n  sorry.\nAdmitted.\n\
         Theorem t : P\nProof.\n  exact lemma.\nQed.\n")

let suite =
  let open Alcotest in
  ( "sorry-admitted",
    [
      test_case "sorry with Admitted. is accepted" `Quick test_sorry_admitted_accepted;
      test_case "sorry with Qed. is rejected" `Quick test_sorry_qed_rejected;
      test_case "transitive sorry with Qed. is rejected" `Quick test_transitive_sorry_qed_rejected;
    ] )
