(* Tests for inferType with stack-based local context *)
open System_e_kernel
open Term
open Infer
open Printexc

let str_contains s sub =
  let n = String.length sub in
  n = 0
  || let rec loop i =
       i + n <= String.length s
       && (String.sub s i n = sub || loop (i + 1))
     in
     loop 0

let mk_env () =
  let env = Hashtbl.create 16 in
  Hashtbl.add env "Point" (Sort 0);
  Hashtbl.add env "Line" (Sort 0);
  Hashtbl.add env "p" (Const "Point");
  Hashtbl.add env "l" (Const "Line");
  env

let test_const_lookup () =
  let env = mk_env () in
  let ty = inferType env [] (Const "Point") in
  assert (ty = Sort 0);
  let ty_line = inferType env [] (Const "Line") in
  assert (ty_line = Sort 0)

let test_fvar_lookup () =
  let env = mk_env () in
  let ty = inferType env [] (Fvar "p") in
  assert (ty = Const "Point")

let test_fvar_unknown_fails () =
  let env = mk_env () in
  try
    ignore (inferType env [] (Fvar "nonexistent"));
    assert false
  with Failure msg -> assert (str_contains msg "unknown free variable")

let test_bvar_stack () =
  let env = mk_env () in
  (* Bvar 0 with [Point] -> Point *)
  let t0 = inferType env [ Const "Point" ] (Bvar 0) in
  assert (t0 = Const "Point");
  (* Bvar 0 = head, Bvar 1 = second; [Line; Point] -> Bvar 0: Line, Bvar 1: Point *)
  let t0' = inferType env [ Const "Line"; Const "Point" ] (Bvar 0) in
  let t1' = inferType env [ Const "Line"; Const "Point" ] (Bvar 1) in
  assert (t0' = Const "Line");
  assert (t1' = Const "Point")

let test_bvar_out_of_scope_fails () =
  let env = mk_env () in
  try
    ignore (inferType env [] (Bvar 0));
    assert false
  with Failure msg -> assert (str_contains msg "out of scope");
  try
    ignore (inferType env [ Const "Point" ] (Bvar 1));
    assert false
  with Failure msg -> assert (str_contains msg "out of scope")

let test_const_unknown_fails () =
  let env = mk_env () in
  try
    ignore (inferType env [] (Const "Unknown"));
    assert false
  with Failure msg -> assert (str_contains msg "unknown constant")

let test_infer_function_type () =
  let env = mk_env () in 

  (* environment used in test contains a variable "p" with type Point *)
  let const_func = Lam (Const "Point", Const "p") in
  assert ((inferType env [] const_func) = Forall (Const "Point", Const "Point"));

  let identity_func = Lam (Const "Point", Bvar 0) in
  assert ((inferType env [] identity_func) = Forall (Const "Point", Const "Point"));
  
  let func_returning_outer_bvar = Lam (Const "Line", Bvar 1) in
  assert ((inferType env [Const "Point"] func_returning_outer_bvar) = Forall (Const "Line", Const "Point"));

  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  assert ((inferType env [] generic_func) = Forall (Sort 1, Forall (Bvar 0, Bvar 0)))

let test_infer_function_application () =
  let env = mk_env () in
  
  (* TODO: try testing case where return type is computed from argument? *)

  let const_func_app = App (Lam (Const "Point", Const "p"), Bvar 0) in
  assert ((inferType env [Const "Point"] const_func_app) = Const "Point");
  try
    ignore (inferType env [Const "Line"] const_func_app);
    assert false
  with Failure msg -> assert (str_contains msg "invalid argument type");

  let identity_func_app = App (Lam (Const "Point", Bvar 0), Const "p") in
  assert ((inferType env [] identity_func_app) = Const "Point");

  let application_with_non_function = App (Const "p", Const "l") in
  try
    ignore (inferType env [] application_with_non_function);
    assert false
  with Failure msg -> assert (str_contains msg "apply non-function to an argument");

  (* TODO: should Point be a Sort 0 or a Sort 1? *)
  (* Corresponds to the expression `(fun (A: Type) -> fun (x: A) -> x) Point` which
  is equivalent to `fun (x: Point) -> x`, so we'd expect a type of `Point => Point` *)
  let generic_func_app = App (Lam (Sort 0, Lam (Bvar 0, Bvar 0)), Const "Point") in
  let inferred_type = inferType env [] generic_func_app in
  assert (inferred_type = Forall (Const "Point", Const "Point"))

let test_subst_bvar () = 
  assert (subst_bvar (Const "Point") 0 (Const "p") = Const "Point");
  assert (subst_bvar (Bvar 0) 0 (Const "p") = Const "p");
  assert (subst_bvar (Bvar 0) 1 (Const "l") = Bvar 0);
  assert (subst_bvar (Bvar 0) 0 (Bvar 5) = Bvar 5);
  (* The inner Bvar 0 refers to the argument to the Lam, so Bvar 0 for the topmost
  expression is Bvar 1 from the point of view of the inner expression *)
  assert (subst_bvar (Lam (Bvar 0, Bvar 0)) 0 (Const "Point") = Lam (Const "Point", Bvar 0));
  assert (subst_bvar (Lam (Bvar 0, Bvar 1)) 0 (Const "Point") = Lam (Const "Point", Const "Point"));
  assert (subst_bvar (Lam (Bvar 0, Bvar 1)) 1 (Const "Point") = Lam (Bvar 0, Bvar 1));

  (* Forall isn't really a function (in the sense that we can't apply it to an expression) 
  but the domain type does act as a bound variable similarly to a Lam, meaning that we
  need to recursively substitute in a Forall as well using the same rules*)
  assert (subst_bvar (Forall (Bvar 0, Bvar 0)) 0 (Sort 5) = Forall (Sort 5, Bvar 0));
  assert (subst_bvar (Forall (Bvar 0, Bvar 1)) 0 (Sort 5) = Forall (Sort 5, Sort 5));
  assert (subst_bvar (Forall (Bvar 0, Bvar 1)) 1 (Sort 5) = Forall (Bvar 0, Bvar 1))


(* These two tests are made my AI so can remove or change them completely if wanted *)
let test_axioms_sanity () =
  let env = mk_axioms_env () in
  (* Base types are Sort 1 *)
  assert (inferType env [] (Const "Len") = Sort 1);
  assert (inferType env [] (Const "Point") = Sort 1);
  (* Zero is an element of Len *)
  assert (inferType env [] (Const "Zero") = Const "Len");
  (* Lt and Add have the right top-level shape *)
  assert (inferType env [] (Const "Lt") =
    Forall (Const "Len", Forall (Const "Len", Sort 0)));
  assert (inferType env [] (Const "Add") =
    Forall (Const "Len", Forall (Const "Len", Const "Len")));
  (* AddZero is exact enough to check de Bruijn encoding *)
  assert (inferType env [] (Const "AddZero") =
    Forall (Const "Len",
      App (App (App (Const "Eq", Const "Len"),
        App (App (Const "Add", Const "Zero"), Bvar 0)),
        Bvar 0)))

let test_axioms_app () =
  let env = mk_axioms_env () in
  (* Lt Zero Zero : Prop *)
  assert (inferType env [] (App (App (Const "Lt", Const "Zero"), Const "Zero")) = Sort 0);
  (* Add Zero Zero : Len *)
  assert (inferType env [] (App (App (Const "Add", Const "Zero"), Const "Zero")) = Const "Len");
  (* LtTrans applied to 3 Len args gives Lt a b -> Lt b c -> Lt a c *)
  Hashtbl.add env "a" (Const "Len");
  Hashtbl.add env "b" (Const "Len");
  Hashtbl.add env "c" (Const "Len");
  let ty = inferType env [] (App (App (App (Const "LtTrans", Fvar "a"), Fvar "b"), Fvar "c") ) in
  assert (ty =
    Forall (App (App (Const "Lt", Fvar "a"), Fvar "b"),
    Forall (App (App (Const "Lt", Fvar "b"), Fvar "c"),
    App (App (Const "Lt", Fvar "a"), Fvar "c"))));
  (* Type mismatch: Lt applied to a Point should fail *)
  Hashtbl.add env "p" (Const "Point");
  try
    ignore (inferType env [] (App (Const "Lt", Fvar "p")));
    assert false
  with Failure _ -> ()

let () =
  (* Taken from https://stackoverflow.com/questions/65868770/lack-of-information-when-ocaml-crashes#comment128358969_65873074,
  turns on stack traces *)
  record_backtrace true;

  test_const_lookup ();
  test_fvar_lookup ();
  test_fvar_unknown_fails ();
  test_bvar_stack ();
  test_bvar_out_of_scope_fails ();
  test_const_unknown_fails ();
  test_infer_function_type ();
  test_subst_bvar ();
  test_infer_function_application ();
  test_axioms_sanity ();
  test_axioms_app ();
  print_endline "All inferType tests passed."
