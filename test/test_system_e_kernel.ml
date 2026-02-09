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

(* --- Dependent pair encoding via constants Exists / Exists.intro --- *)
let type0 = Sort 0                 (* "Type" *)
let pi (a : term) (b : term) = Forall (a, b)  (* Π (_ : a), b *)
let app2 f x y = App (App (f, x), y)

let exists_ty : term =
  pi type0
    (pi (pi (Bvar 0) type0)
        type0)

let exists_intro_ty : term =
  pi type0
    (pi (pi (Bvar 0) type0)
      (pi (Bvar 1)
        (pi (App (Bvar 1, Bvar 0))
          (app2 (Const "Exists") (Bvar 3) (Bvar 2)))))

let add_exists (env : environment) : unit =
  Hashtbl.replace env "Exists" exists_ty;
  Hashtbl.replace env "Exists.intro" exists_intro_ty

let add_unit (env : environment) : unit =
  Hashtbl.replace env "Unit" (Sort 0);
  Hashtbl.replace env "star" (Const "Unit")

let test_exists_constants_lookup () =
  let env = mk_env () in
  add_exists env;
  add_unit env;
  (* Check that the constants are registered with the expected types *)
  assert (inferType env [] (Const "Exists") = exists_ty);
  assert (inferType env [] (Const "Exists.intro") = exists_intro_ty);
  (* Also sanity-check that Unit/star work in the environment *)
  assert (inferType env [] (Const "Unit") = Sort 0);
  assert (inferType env [] (Const "star") = Const "Unit")



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
  test_exists_constants_lookup ();
  print_endline "All inferType tests passed."
