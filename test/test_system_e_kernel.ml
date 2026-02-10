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
  Hashtbl.add env "Point" (Sort 1);
  Hashtbl.add env "Line" (Sort 1);
  Hashtbl.add env "p" (Const "Point");
  Hashtbl.add env "l" (Const "Line");
  env

let test_const_lookup () =
  let env = mk_env () in
  let ty = inferType env (Hashtbl.create 0) (Const "Point") in
  assert (ty = Sort 1);
  let ty_line = inferType env (Hashtbl.create 0) (Const "Line") in
  assert (ty_line = Sort 1)

let test_fvar_lookup () =
  let env = mk_env () in
  let local_ctx = Hashtbl.create 16 in
  Hashtbl.add local_ctx "p1" (Const "Point");
  let ty = inferType env local_ctx (Fvar "p1") in
  assert (ty = Const "Point")

let test_fvar_unknown_fails () =
  let env = mk_env () in
  try
    ignore (inferType env (Hashtbl.create 0) (Fvar "nonexistent"));
    assert false
  with Failure msg -> assert (str_contains msg "unknown free variable")

let test_const_unknown_fails () =
  let env = mk_env () in
  try
    ignore (inferType env (Hashtbl.create 0) (Const "Unknown"));
    assert false
  with Failure msg -> assert (str_contains msg "unknown constant")

let test_empty_constants () =
  (* Empty and Empty.elim live in the axioms env *)
  let env = Infer.mk_axioms_env () in
  (* Empty : Type (i.e. Sort 1) *)
  let empty_ty = inferType env [] (Const "Empty") in
  assert (empty_ty = Sort 1);
  (* Empty.elim : (C : Type) -> Empty -> C *)
  let elim_ty = inferType env [] (Const "Empty.elim") in
  (match elim_ty with
   | Forall (Sort 1, Forall (Const "Empty", Bvar 1)) -> ()
   | _ -> assert false)

let test_and_constants () =
  let env = Infer.mk_axioms_env () in
  (* And : (A : Prop) -> (B : Prop) -> Prop *)
  let and_ty = inferType env [] (Const "And") in
  assert (and_ty = Forall (Sort 0, Forall (Sort 0, Sort 0)));
  (* And.intro : (A : Prop) -> (B : Prop) -> (a : A) -> (b : B) -> And A B *)
  let intro_ty = inferType env [] (Const "And.intro") in
  (match intro_ty with
   | Forall (Sort 0, Forall (Sort 0, Forall (Bvar 1, Forall (Bvar 2, App (App (Const "And", Bvar 3), Bvar 2))))) -> ()
   | _ -> assert false);
  (* And.elim : (A : Prop) -> (B : Prop) -> (C : Type) -> (f : A -> B -> C) -> (h : And A B) -> C *)
  let elim_ty = inferType env [] (Const "And.elim") in
  (match elim_ty with
   | Forall (Sort 0, Forall (Sort 0, Forall (Sort 1, Forall (Forall (Bvar 4, Forall (Bvar 3, Bvar 2)), Forall (App (App (Const "And", Bvar 4), Bvar 3), Bvar 2))))) -> ()
   | _ -> assert false)

let test_infer_function_type () =
  let env = mk_env () in 

  (* environment used in test contains a variable "p" with type Point *)
  let const_func = Lam (Const "Point", Const "p") in
  assert ((inferType env (Hashtbl.create 0) const_func) = Forall (Const "Point", Const "Point"));
  let identity_func = Lam (Const "Point", Bvar 0) in
  assert ((inferType env (Hashtbl.create 0) identity_func) = Forall (Const "Point", Const "Point"));

  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  assert ((inferType env (Hashtbl.create 0) generic_func) = Forall (Sort 1, Forall (Bvar 0, Bvar 1)))

let test_infer_forall () = 
  let env = mk_env () in 

  (* functions Point -> Point should be Type *)
  let forall_term = Forall (Const "Point", Const "Point") in
  assert ((inferType env (Hashtbl.create 0) forall_term) = Sort 1);

  (* fun T: Type => (fun (t: T) => t) *)
  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  let generic_func_type = inferType env (Hashtbl.create 0) generic_func in
  assert (generic_func_type = Forall (Sort 1, Forall (Bvar 0, Bvar 1)));
  (* (T: Type) -> (T -> T) should be Type 1 (= Sort 2) *)
  let generic_func_type_type = inferType env (Hashtbl.create 0) generic_func_type in
  assert (generic_func_type_type = Sort 2);

  (* predicate *)
  let predicate = Forall (Const "Point", Sort 0) in
  Hashtbl.add env "IsRed" predicate;
  (* for all points p, p isRed -> p isRed *)
  let pred_forall = Forall (Const "Point", Forall (App (Const "IsRed", Bvar 0), App (Const "IsRed", Bvar 1))) in
  (* the forall statement is a Prop by impredicativity *)
  assert ((inferType env (Hashtbl.create 0) pred_forall) = Sort 0);
  let bigger_pred_forall = Forall (Sort 67, App (Const "IsRed", Const "p")) in
  assert ((inferType env (Hashtbl.create 0) bigger_pred_forall) = Sort 0);
  (* not a prop, something like fun (p: Point) => p=p like what you might see as a motive in eliminators *)
  let motive = Forall (Const "Point", Sort 0) in
  (* (Point -> Prop) : Type *)
  assert ((inferType env (Hashtbl.create 0) motive) = Sort 1);

  (* failure cases *)
  let return_type_not_sort = Forall (Const "Point", Const "p") in
  assert (try
    ignore (inferType env (Hashtbl.create 0) return_type_not_sort);
    false  
  with Failure msg -> str_contains msg "Return type of a Forall must be a sort");
  let domain_type_not_sort = Forall (Const "p", App (Const "IsRed", Const "p")) in
  assert (try
    ignore (inferType env (Hashtbl.create 0) domain_type_not_sort);
    false  
  with Failure msg -> str_contains msg "Domain type of a Forall must be a sort");
  let domain_and_return_type_not_sort = Forall (Const "p", Const "p") in
  assert (try
    ignore (inferType env (Hashtbl.create 0) domain_and_return_type_not_sort);
    false  
  with Failure msg -> str_contains msg "Domain and return types of a Forall must be sorts")


let test_infer_function_application () =
  let env = mk_env () in 
  
  (* TODO: try testing case where return type is computed from argument? *)

  let local_ctx = Hashtbl.create 16 in
  Hashtbl.add local_ctx "p1" (Const "Point");
  let const_func_app = App (Lam (Const "Point", Const "p"), Fvar "p1") in
  assert ((inferType env local_ctx const_func_app) = Const "Point");
  Hashtbl.clear local_ctx;
  Hashtbl.add local_ctx "l1" (Const "Line");
  try
    ignore (inferType env local_ctx const_func_app);
    assert false
  with Failure msg -> assert (str_contains msg "unknown free variable");
  Hashtbl.clear local_ctx;
  let identity_func_app = App (Lam (Const "Point", Bvar 0), Const "p") in
  assert ((inferType env local_ctx identity_func_app) = Const "Point");

  let application_with_non_function = App (Const "p", Const "l") in
  try
    ignore (inferType env local_ctx application_with_non_function);
    assert false
  with Failure msg -> assert (str_contains msg "apply non-function to an argument");

  (* TODO: should Point be a Sort 0 or a Sort 1? *)
  (* Corresponds to the expression `(fun (A: Type) -> fun (x: A) -> x) Point` which
  is equivalent to `fun (x: Point) -> x`, so we'd expect a type of `Point => Point` *)
  let generic_func_app = App (Lam (Sort 1, Lam (Bvar 0, Bvar 0)), Const "Point") in
  let inferred_type = inferType env local_ctx generic_func_app in
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

let test_app_multiarg () =
  let t = application_multiple_arguments (Const "f") [Const "a"; Const "b"; Const "c"] in
  let expected = App (App (App (Const "f", Const "a"), Const "b"), Const "c") in
  assert (t = expected)


let test_rebind_bvar () = 
  assert (rebind_bvar (Const "Point") 0 "p" = Const "Point");
  assert (rebind_bvar (Fvar "p") 0 "p" = Bvar 0);
  assert (rebind_bvar (Fvar "p") 0 "l" = Fvar "p");
  assert (rebind_bvar (Fvar "p") 1 "p" = Bvar 1);
  assert (rebind_bvar (Bvar 0) 0 "p" = Bvar 0);
  assert (rebind_bvar (Bvar 5) 0 "p" = Bvar 5);
  assert (rebind_bvar (Bvar 0) 5 "p" = Bvar 0);
  assert (rebind_bvar (Bvar 5) 5 "p" = Bvar 5);

  assert (rebind_bvar (Lam (Fvar "Point", Bvar 0)) 0 "Point" = Lam (Bvar 0, Bvar 0));
  assert (rebind_bvar (Lam (Fvar "Point", Fvar "Point")) 0 "Point" = Lam (Bvar 0, Bvar 1));
  assert (rebind_bvar (Lam (Fvar "Point", Fvar "Line")) 0 "Point" = Lam (Bvar 0, Fvar "Line"));
  assert (rebind_bvar (Lam (Bvar 0, Bvar 1)) 1 "Point" = Lam (Bvar 0, Bvar 1))


let () =
  (* Taken from https://stackoverflow.com/questions/65868770/lack-of-information-when-ocaml-crashes#comment128358969_65873074,
  turns on stack traces *)
  record_backtrace true;

  test_const_lookup ();
  test_fvar_lookup ();
  test_fvar_unknown_fails ();
  test_const_unknown_fails ();
  test_infer_function_type ();
  test_infer_forall ();
  test_subst_bvar ();
  test_rebind_bvar ();
  test_infer_function_application ();
  test_app_multiarg ();
  test_empty_constants ();
  test_and_constants ();
  print_endline "All inferType tests passed."
