(* Tests and examples for the pretty-printing feature.
   Run with: dune exec test/test_pretty.exe *)

open E_elab.Kernel_pretty
open E_elab.Decl
open E_elab.Pretty
module KTerm = Nicegeo.Term
module ETerm = E_elab.Term
module Elab = E_elab.Elab

let () = Printf.printf "=== Kernel term pretty-printing ===\n\n"

(* Example 1 *)
let () =
  let t = KTerm.(Forall (Sort 1, Forall (Sort 0, Sort 0))) in
  let pretty = term_to_string_pretty t in
  Printf.printf "Kernel term: Forall (Sort 1, Forall (Sort 0, Sort 0))\n";
  Printf.printf "  Pretty:         %s\n\n" pretty

(* Example 2: Bound variables become _0, _1 instead of Bvar 0, Bvar 1 *)
let () =
  (* (A : Type) -> (B : Prop) -> And A B  with bvars in body *)
  let body = KTerm.(App (App (Const "And", Bvar 1), Bvar 0)) in
  let t = KTerm.(Forall (Sort 1, Forall (Sort 0, body))) in
  Printf.printf "Kernel term with Bvars: (A : Type) -> (B : Prop) -> And A B\n";
  Printf.printf "  Pretty: %s\n\n" (term_to_string_pretty t)

(* Example 3: Optional names for binders *)
let () =
  let t = KTerm.(Forall (Sort 1, Forall (Sort 0, Bvar 0))) in
  Printf.printf "With default names: %s\n" (term_to_string_pretty t);
  (* ~names supplies names for Bvar indices: 0 -> "A", 1 -> "B". Binders still _0,_1. *)
  Printf.printf "With custom names (for Bvars): %s\n\n"
    (term_to_string_pretty ~names:[ "A"; "B" ] t)

(* Example 4: Application flattening *)
let () =
  let t =
    KTerm.(App (App (App (Const "f", Const "a"), Const "b"), Const "c"))
  in
  Printf.printf "App spine f a b c:\n";
  Printf.printf "  Pretty: %s\n\n" (term_to_string_pretty t)

let () = Printf.printf "=== Elaborator term pretty-printing ===\n\n"
let e = Elab.create ()

(* Example 5: Elaborator terms have names already *)
let () =
  let t = ETerm.(Arrow (Some "A", Sort 1, Arrow (Some "B", Sort 0, Bvar 0))) in
  Printf.printf "Elab term (A : Type) -> (B : Prop) -> B:\n";
  Printf.printf "  %s\n\n" (term_to_string e t)

(* Example 6: Declaration pretty-printing *)
let () =
  let d = Axiom ("Point", ETerm.Sort 1) in
  Printf.printf "Axiom Point : Type  =>  %s\n" (decl_to_string e d);
  let d2 =
    Theorem
      ( "id",
        ETerm.(Arrow (Some "A", Sort 1, Arrow (Some "x", Name "A", Bvar 1))),
        ETerm.(Fun (Some "A", Sort 1, Fun (Some "x", Name "A", Bvar 0))) )
  in
  Printf.printf "Theorem id : (A : Type) -> (x : A) -> A := ...  => \n%s\n\n"
    (decl_to_string e d2)

let test_kernel_sort_names () =
  Alcotest.check' Alcotest.string ~msg:"Sort 0 pretty-prints as Prop"
    ~expected:"Prop"
    ~actual:(term_to_string_pretty (KTerm.Sort 0));

  Alcotest.check' Alcotest.string ~msg:"Sort 1 pretty-prints as Type"
    ~expected:"Type"
    ~actual:(term_to_string_pretty (KTerm.Sort 1))

let test_elab_hole () =
  Alcotest.check' Alcotest.string ~msg:"Hole 0 pretty-prints as ?m0"
    ~expected:"?m0"
    ~actual:(term_to_string e (ETerm.Hole 0))

let test_elab_arrow_no_name () =
  let t = ETerm.(Arrow (None, Sort 1, Sort 0)) in
  Alcotest.check' Alcotest.string ~msg:"arrow pretty-prints sorts"
    ~expected:"Type -> Prop" ~actual:(term_to_string e t)

let suite =
  let open Alcotest in
  ( "Pretty-printing",
    [
      test_case "Kernel sort names" `Quick test_kernel_sort_names;
      test_case "Elab hole" `Quick test_elab_hole;
      test_case "Elab arrow no name" `Quick test_elab_arrow_no_name;
    ] )
