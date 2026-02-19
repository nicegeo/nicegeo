open System_e_kernel
open Term
open Infer
open Printexc
open E_elab

(* reduce originally had domainType = arg_type instead of isDefEq, which would cause this to fail *)
let test_reduce_crashes () =
  let env = (Elab.create_with_env ()).kenv in
  let ctx = Hashtbl.create 0 in
  Hashtbl.add ctx "p" (Const "Point");
  let fancy_point = App (Lam (Sort 1, Bvar 0), Const "Point") in
  let term = App (Lam (fancy_point, Bvar 0), Fvar "p") in
  let result = reduce env ctx term in
  assert (result = Fvar "p")

(* two Apps makes things not reduce all the way although i'm not sure if this would come up in practice*)
let test_reduce_stuck () =
  let env = (Elab.create_with_env ()).kenv in
  let ctx = Hashtbl.create 0 in
  Hashtbl.add ctx "p" (Const "Point");
  let term = App (App (Lam (Sort 1, Lam (Bvar 0, Bvar 0)), Const "Point"), Fvar "p") in
  let result = reduce env ctx term in
  assert (result = Fvar "p")

(* this test failed for the same reason that test_reduce_stuck failed *)
let test_isDefEq_forall () =
  let env = (Elab.create_with_env ()).kenv in
  let ctx = Hashtbl.create 0 in
  let lhs = App (App (
    Lam (Sort 1, Lam (Sort 1, Forall (Bvar 1, Bvar 1))),
    Const "Point"), Const "Line") in
  let rhs = Forall (Const "Point", Const "Line") in
  assert (isDefEq env ctx lhs rhs)

let () =
  record_backtrace true;

  test_reduce_crashes ();
  test_reduce_stuck ();
  test_isDefEq_forall ();

  print_endline "All adversarial tests passed."