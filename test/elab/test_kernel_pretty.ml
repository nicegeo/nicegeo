open Elab.Kernel_pretty

let () = Printf.printf "=== Kernel term pretty-printing ===\n\n"

(* Example 1 *)
let () =
  let t = Kernel.Term.(Forall (Sort 1, Forall (Sort 0, Sort 0))) in
  let pretty = term_to_string_pretty t in
  Printf.printf "Kernel term: Forall (Sort 1, Forall (Sort 0, Sort 0))\n";
  Printf.printf "  Pretty:         %s\n\n" pretty

(* Example 2: Bound variables become _0, _1 instead of Bvar 0, Bvar 1 *)
let () =
  (* (A : Type) -> (B : Prop) -> And A B  with bvars in body *)
  let body = Kernel.Term.(App (App (Const "And", Bvar 1), Bvar 0)) in
  let t = Kernel.Term.(Forall (Sort 1, Forall (Sort 0, body))) in
  Printf.printf "Kernel term with Bvars: (A : Type) -> (B : Prop) -> And A B\n";
  Printf.printf "  Pretty: %s\n\n" (term_to_string_pretty t)

(* Example 3: Optional names for binders *)
let () =
  let t = Kernel.Term.(Forall (Sort 1, Forall (Sort 0, Bvar 0))) in
  Printf.printf "With default names: %s\n" (term_to_string_pretty t);
  (* ~names supplies names for Bvar indices: 0 -> "A", 1 -> "B". Binders still _0,_1. *)
  Printf.printf
    "With custom names (for Bvars): %s\n\n"
    (term_to_string_pretty ~names:[ "A"; "B" ] t)

(* Example 4: Application flattening *)
let () =
  let t = Kernel.Term.(App (App (App (Const "f", Const "a"), Const "b"), Const "c")) in
  Printf.printf "App spine f a b c:\n";
  Printf.printf "  Pretty: %s\n\n" (term_to_string_pretty t)

let test_kernel_sort_names () =
  Alcotest.check'
    Alcotest.string
    ~msg:"Sort 0 pretty-prints as Prop"
    ~expected:"Prop"
    ~actual:(term_to_string_pretty (Kernel.Term.Sort 0));

  Alcotest.check'
    Alcotest.string
    ~msg:"Sort 1 pretty-prints as Type"
    ~expected:"Type"
    ~actual:(term_to_string_pretty (Kernel.Term.Sort 1))

let suite =
  let open Alcotest in
  ( "Kernel Pretty-printing",
    [ test_case "Kernel sort names" `Quick test_kernel_sort_names ] )
