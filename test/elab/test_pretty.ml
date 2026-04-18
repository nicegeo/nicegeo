(* Tests and examples for the pretty-printing feature.
   Run with: dune exec test/test_pretty.exe *)

open Elab.Pretty

let e = Elab.Interface.create ()
let l = Elab.Term.dummy_range

let test_lam_flattening () =
  Alcotest.check'
    Alcotest.string
    ~msg:"Lambda args pretty-prints flattened"
    ~expected:"fun (x : A) (y : B) => x"
    ~actual:
      (term_to_string e Util.(nfun "x" 1 (name "A") (nfun "y" 2 (name "B") (bvar 1))));

  Alcotest.check'
    Alcotest.string
    ~msg:"Dependent lambda arg flattening"
    ~expected:"fun (x : A) (y : B x) => y"
    ~actual:
      (term_to_string
         e
         Util.(nfun "x" 1 (name "A") (nfun "y" 2 (app (name "B") (bvar 1)) (bvar 2))))

let test_elab_hole () =
  Alcotest.check'
    Alcotest.string
    ~msg:"Hole 0 pretty-prints as ?m0"
    ~expected:"?m0"
    ~actual:(term_to_string e { inner = Hole 0; loc = l })

let test_elab_arrow_no_name () =
  let t = Util.(uarrow 1 (sort 1) (sort 0)) in
  Alcotest.check'
    Alcotest.string
    ~msg:"arrow pretty-prints sorts"
    ~expected:"Type → Prop"
    ~actual:(term_to_string e t)

let test_arrow_assoc () =
  let t = Util.(uarrow 1 (sort 0) (uarrow 2 (sort 0) (sort 0))) in
  Alcotest.check'
    Alcotest.string
    ~msg:"arrow pretty-prints right-associative"
    ~expected:"Prop → Prop → Prop"
    ~actual:(term_to_string e t);

  let t = Util.(uarrow 1 (uarrow 2 (sort 0) (sort 0)) (sort 0)) in
  Alcotest.check'
    Alcotest.string
    ~msg:"arrow pretty-prints right-associative even when left-arg is arrow"
    ~expected:"(Prop → Prop) → Prop"
    ~actual:(term_to_string e t);

  ()

let test_app_parens () =
  let t = Util.(app (app (name "f") (name "x")) (name "y")) in
  Alcotest.check'
    Alcotest.string
    ~msg:"application pretty-prints left-associative without parens"
    ~expected:"f x y"
    ~actual:(term_to_string e t);

  let t = Util.(app (name "f") (app (name "x") (name "y"))) in
  Alcotest.check'
    Alcotest.string
    ~msg:"application pretty-prints left-associative with parens"
    ~expected:"f (x y)"
    ~actual:(term_to_string e t);
  ()

let test_lam_app () =
  let t = Util.(nfun "x" 1 (name "A") (app (name "f") (bvar 1))) in
  Alcotest.check'
    Alcotest.string
    ~msg:"Lambda body pretty-prints with correct precedence"
    ~expected:"fun (x : A) => f x"
    ~actual:(term_to_string e t);

  let t = Util.(app (nfun "x" 1 (name "A") (bvar 1)) (name "y")) in
  Alcotest.check'
    Alcotest.string
    ~msg:"Lambda pretty-prints with parens when used as application fun"
    ~expected:"(fun (x : A) => x) y"
    ~actual:(term_to_string e t);

  let t = Util.(app (name "f") (nfun "x" 1 (name "A") (bvar 1))) in
  Alcotest.check'
    Alcotest.string
    ~msg:"Lambda arg pretty-prints with parens when used as application arg"
    ~expected:"f (fun (x : A) => x)"
    ~actual:(term_to_string e t);
  ()

let test_notation () =
  let t = Util.(app (name "Not") (name "P")) in
  Alcotest.check'
    Alcotest.string
    ~msg:"Not pretty-prints with ¬ notation"
    ~expected:"¬P"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Exists A (fun (a : A) => B)" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Exists pretty-prints with ∃ notation"
    ~expected:"∃ (a : A), B"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Iff P Q" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Iff pretty-prints with ↔ notation"
    ~expected:"P ↔ Q"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Or P Q" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Or pretty-prints with ∨ notation"
    ~expected:"P ∨ Q"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "And P Q" in
  Alcotest.check'
    Alcotest.string
    ~msg:"And pretty-prints with ∧ notation"
    ~expected:"P ∧ Q"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Lt x y" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Lt pretty-prints with < notation"
    ~expected:"x < y"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Eq A x y" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Eq pretty-prints with = notation"
    ~expected:"x = y"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Eq A" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Partially applied Eq pretty-prints without = notation"
    ~expected:"Eq A"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Ne A x y" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Ne pretty-prints with ≠ notation"
    ~expected:"x ≠ y"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "Add x y" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Add pretty-prints with + notation"
    ~expected:"x + y"
    ~actual:(term_to_string e t);

  ()

let test_notation_prec () =
  let t =
    Util.(
      app
        (app
           (app (name "Eq") (name "Measure"))
           (app (app (name "Add") (name "x")) (name "y")))
        (app (app (name "Add") (name "z")) (name "w")))
  in
  Alcotest.check'
    Alcotest.string
    ~msg:"Notations pretty-print with correct precedence"
    ~expected:"x + y = z + w"
    ~actual:(term_to_string e t);

  (* this is a pretty confusing expression, perhaps we shouldn't allow A → B ↔ C in the language *)
  (* but i'm not sure how to change that (currently it's parsed as `A → (B ↔ C)`) *)
  let t = Elab.Interface.parse_term "(¬P ↔ Q) → Q ↔ a + b < c" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Notations pretty-print with precedence matching parser"
    ~expected:"(¬P ↔ Q) → Q ↔ a + b < c"
    ~actual:(term_to_string e t);

  let t = Elab.Interface.parse_term "¬P ∨ Q ∧ R" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Notations pretty-print with precedence matching parser (2)"
    ~expected:"¬P ∨ Q ∧ R"
    ~actual:(term_to_string e t);
  
  let t = Elab.Interface.parse_term "f P (¬Q) R" in
  Alcotest.check'
    Alcotest.string
    ~msg:"Function application with negation"
    ~expected:"f P (¬Q) R"
    ~actual:(term_to_string e t);

  ()

let suite =
  let open Alcotest in
  ( "Pretty-printing",
    [
      test_case "Function args flattened" `Quick test_lam_flattening;
      test_case "Elab hole" `Quick test_elab_hole;
      test_case "Elab arrow no name" `Quick test_elab_arrow_no_name;
      test_case "Arrow right-associative" `Quick test_arrow_assoc;
      test_case "Application left-associative" `Quick test_app_parens;
      test_case "Lambda application" `Quick test_lam_app;
      test_case "Notation" `Quick test_notation;
      test_case "Notation precedence" `Quick test_notation_prec;
    ] )
