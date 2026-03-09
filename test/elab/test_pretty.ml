(* Tests and examples for the pretty-printing feature.
   Run with: dune exec test/test_pretty.exe *)

open Elab.Decl
open Elab.Pretty
module ETerm = Elab.Term
module Nice = Elab.Nice_messages
module ElabIf = Elab.Interface

let () = Printf.printf "=== Elaborator term pretty-printing ===\n\n"
let e = ElabIf.create ()
let l = ETerm.dummy_range

(* Example 1: Elaborator terms have names already *)
let () =
  let t = Util.(nfun "A" (sort 1) (nfun "B" (sort 0) (bvar 0))) in
  Printf.printf "Elab term (A : Type) -> (B : Prop) -> B:\n";
  Printf.printf "  %s\n\n" (term_to_string e t)

(* Example 2: Declaration pretty-printing *)
let () =
  let d =
    { name = "Point"; name_loc = l; ty = { ETerm.inner = Sort 1; loc = l }; kind = Axiom }
  in
  Printf.printf "Axiom Point : Type  =>  %s\n" (decl_to_string e d);
  let d2 =
    {
      name = "id";
      name_loc = l;
      ty = Util.(narrow "A" (sort 1) (narrow "x" (bvar 0) (bvar 1)));
      kind = Theorem Util.(ufun (sort 1) (ufun (bvar 0) (bvar 0)));
    }
  in
  Printf.printf
    "Theorem id : (A : Type) -> (x : A) -> A := ...  => \n%s\n\n"
    (decl_to_string e d2)

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
    ~actual:(term_to_string e { ETerm.inner = Hole 0; loc = l })

let test_elab_arrow_no_name () =
  let t = Util.(uarrow (sort 1) (sort 0)) in
  Alcotest.check'
    Alcotest.string
    ~msg:"arrow pretty-prints sorts"
    ~expected:"Type -> Prop"
    ~actual:(term_to_string e t)

let test_nice_default_tone_calm () =
  (* OCaml versions vary on [Unix.unsetenv]. Simulate “unset/unknown” by using an unrecognized value. *)
  Unix.putenv "NICEGEO_TONE" "unknown";
  match Nice.tone_from_env () with
  | Nice.Calm -> ()
  | _ -> Alcotest.fail "Expected Calm when NICEGEO_TONE is unset/unknown"

let test_nice_tone_from_env_cheerful () =
  Unix.putenv "NICEGEO_TONE" "cheerful";
  match Nice.tone_from_env () with
  | Nice.Cheerful -> ()
  | _ -> Alcotest.fail "Expected Cheerful when NICEGEO_TONE=cheerful"

let test_nice_pick_message_after_error () =
  match Nice.pick_message Nice.Calm Nice.After_error with
  | Some msg when msg <> "" -> ()
  | _ -> Alcotest.fail "Expected a non-empty encouragement message"

let suite =
  let open Alcotest in
  ( "Pretty-printing",
    [
      test_case "Elab hole" `Quick test_elab_hole;
      test_case "Elab arrow no name" `Quick test_elab_arrow_no_name;
      test_case "Function args flattened" `Quick test_lam_flattening;
      test_case "Nice messages: default tone" `Quick test_nice_default_tone_calm;
      test_case "Nice messages: env cheerful" `Quick test_nice_tone_from_env_cheerful;
      test_case
        "Nice messages: pick after error"
        `Quick
        test_nice_pick_message_after_error;
    ] )
