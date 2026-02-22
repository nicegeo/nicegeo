(* Tests and examples for the pretty-printing feature.
   Run with: dune exec test/test_pretty.exe *)

open System_e_kernel
open System_e_kernel.Pretty
open E_elab.Decl
open E_elab.Pretty

module KTerm = System_e_kernel.Term
module ETerm = E_elab.Term

let () = Printf.printf "=== Kernel term pretty-printing ===\n\n"

(* Example 1: Raw kernel term_to_string (from Infer) vs our pretty version *)
let () =
  let t = KTerm.(Forall (Sort 1, Forall (Sort 0, Sort 0))) in
  let raw = Infer.term_to_string t in
  let pretty = term_to_string_pretty t in
  Printf.printf "Kernel term: Forall (Sort 1, Forall (Sort 0, Sort 0))\n";
  Printf.printf "  Raw (Infer):    %s\n" raw;
  Printf.printf "  Pretty:         %s\n\n" pretty

(* Example 2: Bound variables become _0, _1 instead of Bvar 0, Bvar 1 *)
let () =
  (* (A : Type) -> (B : Prop) -> And A B  with bvars in body *)
  let body =
    KTerm.(App (App (Const "And", Bvar 1), Bvar 0))
  in
  let t = KTerm.(Forall (Sort 1, Forall (Sort 0, body))) in
  Printf.printf "Kernel term with Bvars: (A : Type) -> (B : Prop) -> And A B\n";
  Printf.printf "  Raw:    %s\n" (Infer.term_to_string t);
  Printf.printf "  Pretty: %s\n\n" (term_to_string_pretty t)

(* Example 3: Optional names for binders *)
let () =
  let t = KTerm.(Forall (Sort 1, Forall (Sort 0, Bvar 0))) in
  Printf.printf "With default names: %s\n" (term_to_string_pretty t);
  (* ~names supplies names for Bvar indices: 0 -> "A", 1 -> "B". Binders still _0,_1. *)
  Printf.printf "With custom names (for Bvars): %s\n\n"
    (term_to_string_pretty ~names:["A"; "B"] t)

(* Example 4: Application flattening *)
let () =
  let t =
    KTerm.(App (App (App (Const "f", Const "a"), Const "b"), Const "c"))
  in
  Printf.printf "App spine f a b c:\n";
  Printf.printf "  Raw:    %s\n" (Infer.term_to_string t);
  Printf.printf "  Pretty: %s\n\n" (term_to_string_pretty t)

let () = Printf.printf "=== Elaborator term pretty-printing ===\n\n"

(* Example 5: Elaborator terms have names already *)
let () =
  let t = ETerm.(Arrow ("A", Sort 1, Arrow ("B", Sort 0, Name "B"))) in
  Printf.printf "Elab term (A : Type) -> (B : Prop) -> B:\n";
  Printf.printf "  %s\n\n" (term_to_string t)

(* Example 6: Declaration pretty-printing *)
let () =
  let d = Axiom ("Point", ETerm.Sort 1) in
  Printf.printf "Axiom Point : Type  =>  %s\n" (decl_to_string d);
  let d2 =
    Theorem
      ( "id",
        ETerm.(Arrow ("A", Sort 1, Arrow ("x", Name "A", Name "A"))),
        ETerm.(Fun ("A", Sort 1, Fun ("x", Name "A", Name "x"))) )
  in
  Printf.printf "Theorem id : (A : Type) -> (x : A) -> A := ...  =>  %s\n\n"
    (decl_to_string d2)

let () = Printf.printf "=== Sanity checks (assertions) ===\n"

let test_kernel_sort_names () =
  assert (term_to_string_pretty (KTerm.Sort 0) = "Prop");
  assert (term_to_string_pretty (KTerm.Sort 1) = "Type")

let test_elab_hole () = assert (term_to_string ETerm.Hole = "_")

let test_elab_arrow_no_name () =
  let t = ETerm.(Arrow ("", Sort 1, Sort 0)) in
  assert (term_to_string t = "Type -> Prop")

let () =
  test_kernel_sort_names ();
  test_elab_hole ();
  test_elab_arrow_no_name ();
  Printf.printf "All assertions passed.\n"
