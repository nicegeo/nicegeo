(* Tests and examples for the pretty-printing feature.
   Run with: dune exec test/test_pretty.exe *)

open Elab.Pretty

let () = Printf.printf "=== Elaborator term pretty-printing ===\n\n"
let e = Elab.Interface.create ()
let l = Elab.Term.dummy_range

(* Example 1: Elaborator terms have names already *)
let () =
  let t = Util.(nfun "A" (sort 1) (nfun "B" (sort 0) (bvar 0))) in
  Printf.printf "Elab term (A : Type) -> (B : Prop) -> B:\n";
  Printf.printf "  %s\n\n" (term_to_string e t)

let test_lam_flattening () =
  Alcotest.check'
    Alcotest.string
    ~msg:"Lambda args pretty-prints flattened"
    ~expected:"fun (x : A) (y : B) => x"
    ~actual:(term_to_string e Util.(nfun "x" (name "A") (nfun "y" (name "B") (bvar 1))));

  Alcotest.check'
    Alcotest.string
    ~msg:"Dependent lambda arg flattening"
    ~expected:"fun (x : A) (y : B x) => y"
    ~actual:
      (term_to_string
         e
         Util.(nfun "x" (name "A") (nfun "y" (app (name "B") (bvar 0)) (bvar 0))))

let test_elab_hole () =
  Alcotest.check'
    Alcotest.string
    ~msg:"Hole 0 pretty-prints as ?m0"
    ~expected:"?m0"
    ~actual:(term_to_string e { inner = Hole 0; loc = l })

let test_elab_arrow_no_name () =
  let t = Util.(uarrow (sort 1) (sort 0)) in
  Alcotest.check'
    Alcotest.string
    ~msg:"arrow pretty-prints sorts"
    ~expected:"Type -> Prop"
    ~actual:(term_to_string e t)

let suite =
  let open Alcotest in
  ( "Pretty-printing",
    [
      test_case "Function args flattened" `Quick test_lam_flattening;
      test_case "Elab hole" `Quick test_elab_hole;
      test_case "Elab arrow no name" `Quick test_elab_arrow_no_name;
    ] )
