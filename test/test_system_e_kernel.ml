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
  assert ((inferType env [Const "Point"] func_returning_outer_bvar) = Forall (Const "Line", Const "Point"))

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
  with Failure msg -> assert (str_contains msg "apply non-function to an argument")

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
  test_infer_function_application ();
  print_endline "All inferType tests passed."
