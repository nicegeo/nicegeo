(* Tests for inferType with stack-based local context *)
open System_e_kernel
open Term
open Infer
open Exceptions
open Printexc
open E_elab

(* For backwards compatibility during exception refactoring *)
let try_infer env localCtx t =
  inferType env localCtx t

let mk_env () =
  let env = Hashtbl.create 16 in
  Hashtbl.add env "Point" (Sort 1);
  Hashtbl.add env "Line" (Sort 1);
  Hashtbl.add env "p" (Const "Point");
  Hashtbl.add env "l" (Const "Line");
  env

let test_const_lookup () =
  let env = mk_env () in
  let ty = try_infer env (Hashtbl.create 0) (Const "Point") in
  assert (ty = Sort 1);
  let ty_line = try_infer env (Hashtbl.create 0) (Const "Line") in
  assert (ty_line = Sort 1)

let test_fvar_lookup () =
  let env = mk_env () in
  let local_ctx = Hashtbl.create 16 in
  Hashtbl.add local_ctx "p1" (Const "Point");
  let ty = try_infer env local_ctx (Fvar "p1") in
  assert (ty = Const "Point")

let test_fvar_unknown_fails () =
  let env = mk_env () in
  try
    ignore (try_infer env (Hashtbl.create 0) (Fvar "nonexistent"));
    assert false
  with TypeError { err_kind; _} -> 
    (match err_kind with
    | UnknownFreeVarError _ -> ()
    | _ -> assert false)

let test_const_unknown_fails () =
  let env = mk_env () in
  try
    ignore (try_infer env (Hashtbl.create 0) (Const "Unknown"));
    assert false
  with TypeError { err_kind; _} -> 
    (match err_kind with
    | UnknownConstError _ -> ()
    | _ -> assert false)

let path_to_env = "../../../elab/env.txt"

let test_empty_constants () =
  (* Empty and Empty.elim live in the axioms env *)
  let env = Elab.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in
  (* Empty : Type (i.e. Sort 1) *)
  let empty_ty = try_infer env.kenv lctx (Const "Empty") in
  assert (empty_ty = Sort 1);
  (* Empty.elim : (C : Type) -> Empty -> C *)
  let elim_ty = try_infer env.kenv lctx (Const "Empty.elim") in
  (match elim_ty with
   | Forall (Sort 1, Forall (Const "Empty", Bvar 1)) -> ()
   | _ -> assert false)

let test_and_constants () =
  let env = Elab.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in
  (* And : (A : Prop) -> (B : Prop) -> Prop *)
  let and_ty = try_infer env.kenv lctx (Const "And") in
  assert (and_ty = Forall (Sort 0, Forall (Sort 0, Sort 0)));
  (* And.intro : (A : Prop) -> (B : Prop) -> (a : A) -> (b : B) -> And A B *)
  let intro_ty = try_infer env.kenv lctx (Const "And.intro") in
  (match intro_ty with
   | Forall (Sort 0, Forall (Sort 0, Forall (Bvar 1, Forall (Bvar 1, App (App (Const "And", Bvar 3), Bvar 2))))) -> ()
   | _ -> assert false);
  (* And.elim : (A : Prop) -> (B : Prop) -> (C : Prop) -> (f : A -> B -> C) -> (h : And A B) -> C *)
  let elim_ty = try_infer env.kenv lctx (Const "And.elim") in
  (match elim_ty with
   | Forall (Sort 0, Forall (Sort 0, Forall (Sort 0, Forall (Forall (Bvar 2, Forall (Bvar 2, Bvar 2)), Forall (App (App (Const "And", Bvar 3), Bvar 2), Bvar 2))))) -> ()
   | _ -> assert false)

let test_infer_function_type () =
  let env = mk_env () in 

  (* environment used in test contains a variable "p" with type Point *)
  let const_func = Lam (Const "Point", Const "p") in
  assert ((try_infer env (Hashtbl.create 0) const_func) = Forall (Const "Point", Const "Point"));
  let identity_func = Lam (Const "Point", Bvar 0) in
  assert ((try_infer env (Hashtbl.create 0) identity_func) = Forall (Const "Point", Const "Point"));

  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  assert ((try_infer env (Hashtbl.create 0) generic_func) = Forall (Sort 1, Forall (Bvar 0, Bvar 1)))

let test_infer_forall () = 
  let env = mk_env () in 

  (* functions Point -> Point should be Type *)
  let forall_term = Forall (Const "Point", Const "Point") in
  assert ((try_infer env (Hashtbl.create 0) forall_term) = Sort 1);

  (* fun T: Type => (fun (t: T) => t) *)
  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  let generic_func_type = try_infer env (Hashtbl.create 0) generic_func in
  assert (generic_func_type = Forall (Sort 1, Forall (Bvar 0, Bvar 1)));
  (* (T: Type) -> (T -> T) should be Type 1 (= Sort 2) *)
  let generic_func_type_type = try_infer env (Hashtbl.create 0) generic_func_type in
  assert (generic_func_type_type = Sort 2);

  (* predicate *)
  let predicate = Forall (Const "Point", Sort 0) in
  Hashtbl.add env "IsRed" predicate;
  (* for all points p, p isRed -> p isRed *)
  let pred_forall = Forall (Const "Point", Forall (App (Const "IsRed", Bvar 0), App (Const "IsRed", Bvar 1))) in
  (* the forall statement is a Prop by impredicativity *)
  assert ((try_infer env (Hashtbl.create 0) pred_forall) = Sort 0);
  let bigger_pred_forall = Forall (Sort 67, App (Const "IsRed", Const "p")) in
  assert ((try_infer env (Hashtbl.create 0) bigger_pred_forall) = Sort 0);
  (* not a prop, something like fun (p: Point) => p=p like what you might see as a motive in eliminators *)
  let motive = Forall (Const "Point", Sort 0) in
  (* (Point -> Prop) : Type *)
  assert ((try_infer env (Hashtbl.create 0) motive) = Sort 1);

  (* failure cases *)
  let return_type_not_sort = Forall (Const "Point", Const "p") in
  assert (try
    ignore (try_infer env (Hashtbl.create 0) return_type_not_sort);
    false  
  with TypeError { err_kind; _} -> 
    (match err_kind with
    | ForallSortError _ -> true
    | _ -> false));
  let domain_type_not_sort = Forall (Const "p", App (Const "IsRed", Const "p")) in
  assert (try
    ignore (try_infer env (Hashtbl.create 0) domain_type_not_sort);
    false  
  with TypeError { err_kind; _} -> 
    (match err_kind with
    | ForallSortError _ -> true
    | _ -> false));
  let domain_and_return_type_not_sort = Forall (Const "p", Const "p") in
  assert (try
    ignore (try_infer env (Hashtbl.create 0) domain_and_return_type_not_sort);
    false  
  with TypeError { err_kind; _} -> 
    (match err_kind with
    | ForallSortError _ -> true
    | _ -> false))


let test_infer_function_application () =
  let env = mk_env () in 
  
  (* TODO: try testing case where return type is computed from argument? *)

  let local_ctx = Hashtbl.create 16 in
  Hashtbl.add local_ctx "p1" (Const "Point");
  let const_func_app = App (Lam (Const "Point", Const "p"), Fvar "p1") in
  assert ((try_infer env local_ctx const_func_app) = Const "Point");
  Hashtbl.clear local_ctx;
  Hashtbl.add local_ctx "l1" (Const "Line");
  try
    ignore (try_infer env local_ctx const_func_app);
    assert false
  with 
  TypeError { err_kind; _} -> 
    (match err_kind with
    | UnknownFreeVarError _ -> ()
    | _ -> assert false);
  Hashtbl.clear local_ctx;
  let identity_func_app = App (Lam (Const "Point", Bvar 0), Const "p") in
  assert ((try_infer env local_ctx identity_func_app) = Const "Point");

  let application_with_non_function = App (Const "p", Const "l") in
  try
    ignore (try_infer env local_ctx application_with_non_function);
    assert false
  with TypeError { err_kind; _} -> 
    (match err_kind with
    | AppNonFuncError -> ()
    | _ -> assert false);

  (* TODO: should Point be a Sort 0 or a Sort 1? *)
  (* Corresponds to the expression `(fun (A: Type) -> fun (x: A) -> x) Point` which
  is equivalent to `fun (x: Point) -> x`, so we'd expect a type of `Point => Point` *)
  let generic_func_app = App (Lam (Sort 1, Lam (Bvar 0, Bvar 0)), Const "Point") in
  let inferred_type = try_infer env local_ctx generic_func_app in
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

let application_multiple_arguments (func: term) (args: term list): term = 
  List.fold_left
    (fun application_so_far first_arg -> App (application_so_far, first_arg))
    func
    args

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

let eq ty a b = App (App (App (Const "Eq", ty), a), b)

let test_eq_symm () = 
  let env = Elab.create_with_env_path path_to_env in
  let local_ctx = Hashtbl.create 16 in
  let eq_symm_type = 
    Forall (Sort 1, (* A: Type *)
    Forall (Bvar 0, (* a: A *)
    Forall (Bvar 1, (* b: A *)
    Forall (eq (Bvar 2) (Bvar 1) (Bvar 0), (* Eq a b *)
    eq (Bvar 3) (Bvar 1) (Bvar 2) (* Eq b a *)
  )))) in
  assert (try_infer env.kenv local_ctx eq_symm_type = Sort 0); (* make sure this is actually a Prop *)
  let eq_symm_term = 
    Lam (Sort 1, (* A: Type *)
    Lam (Bvar 0, (* a: A *)
    Lam (Bvar 1, (* b: A *)
    Lam (eq (Bvar 2) (Bvar 1) (Bvar 0), (* eq_ab: Eq a b *)
      application_multiple_arguments (Const "Eq.elim") [
        Bvar 3; (* A: Type *)
        Bvar 2; (* a: A *)
        (Lam (Bvar 3, eq (Bvar 4) (Bvar 0) (Bvar 3))); (* motive: A -> Prop *)
        App (App (Const "Eq.intro", (Bvar 3)), (Bvar 2)); (* refl: motive a *)
        Bvar 1; (* b: A *)
        Bvar 0 (* eq_ab: Eq a b *)
      ]
    )))) in
  (* print_endline ("eq_symm_term: " ^ (term_to_string eq_symm_term)); *)
  let inferred_type = try_infer env.kenv local_ctx eq_symm_term in
  (* print_endline ("expected eq_symm_type: " ^ (term_to_string eq_symm_type));
  print_endline ("inferred eq_symm_type: " ^ (term_to_string inferred_type)); *)
  assert (isDefEq env.kenv local_ctx inferred_type eq_symm_type)


(* These two tests are made by AI so can remove or change them completely if wanted *)
let test_len_sanity () =
  let env = Elab.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in
  (* Base types are Sort 1 *)
  assert (try_infer env.kenv lctx (Const "Len") = Sort 1);
  assert (try_infer env.kenv lctx (Const "Point") = Sort 1);
  (* Zero is an element of Len *)
  assert (try_infer env.kenv lctx (Const "Zero") = Const "Len");
  (* Lt and Add have the right top-level shape *)
  assert (try_infer env.kenv lctx (Const "Lt") =
    Forall (Const "Len", Forall (Const "Len", Sort 0)));
  assert (try_infer env.kenv lctx (Const "Add") =
    Forall (Const "Len", Forall (Const "Len", Const "Len")));
  (* AddZero is exact enough to check de Bruijn encoding *)
  let inferred = (try_infer env.kenv lctx (Const "AddZero")) in
  let expected = (Forall (Const "Len",
      App (App (App (Const "Eq", Const "Len"),
        App (App (Const "Add", Bvar 0), Const "Zero")),
        Bvar 0))) in
  assert (isDefEq env.kenv lctx inferred expected)

let test_len_app () =
  let env = Elab.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in
  (* Lt Zero Zero : Prop *)
  assert (try_infer env.kenv lctx (App (App (Const "Lt", Const "Zero"), Const "Zero")) = Sort 0);
  (* Add Zero Zero : Len *)
  assert (try_infer env.kenv lctx (App (App (Const "Add", Const "Zero"), Const "Zero")) = Const "Len");
  (* LtTrans applied to 3 Len args gives Lt a b -> Lt b c -> Lt a c *)
  Hashtbl.add lctx "a" (Const "Len");
  Hashtbl.add lctx "b" (Const "Len");
  Hashtbl.add lctx "c" (Const "Len");
  let ty = try_infer env.kenv lctx (App (App (App (Const "LtTrans", Fvar "a"), Fvar "b"), Fvar "c") ) in
  assert (ty =
    Forall (App (App (Const "Lt", Fvar "a"), Fvar "b"),
    Forall (App (App (Const "Lt", Fvar "b"), Fvar "c"),
    App (App (Const "Lt", Fvar "a"), Fvar "c"))));
  (* Type mismatch: Lt applied to a Point should fail *)
  Hashtbl.add lctx "p" (Const "Point");
  try
    ignore (try_infer env.kenv lctx (App (Const "Lt", Fvar "p")));
    assert false
  with TypeError _ -> ()

let test_kernel_reduce () = 
  (* (fun (p1: Point) => (fun (p2: Point) => p2)) p) l *)
  (* should be reduced to (fun (p2: Point) => p2) l then to l *)
  let env = mk_env () in
  let lctx = Hashtbl.create 16 in
  let term = App (App (Lam (Const "Point", Lam (Const "Point", Bvar 0)), Const "p"), Const "l") in
  let reduced = reduce env lctx term in
  assert (reduced = Const "l");

  (* fun (x: (fun a => Point) p) => x is well-typed and should not fail inference *)
  (* (reduces to fun (x: Point) => x) *)
  let term = Lam (App (Lam (Const "Point", Const "Point"), Const "p"), Bvar 0) in
  assert (isDefEq env lctx (inferType env lctx term) (Forall (Const "Point", Const "Point")));
  (* (fun a => Point) p -> Point is well-typed and should not fail inference *)
  (* (reduces to Point -> Point) *)
  let term = Forall (App (Lam (Const "Point", Const "Point"), Const "p"), Const "Point") in
  assert (isDefEq env lctx (inferType env lctx term) (Sort 1));
  (* Point -> (fun a => Point) p *)
  let term = Forall (Const "Point", App (Lam (Const "Point", Const "Point"), Const "p")) in
  assert (isDefEq env lctx (inferType env lctx term) (Sort 1));
  (* (fun a => Point) p -> (fun a => Point) p *)
  let term = Forall (App (Lam (Const "Point", Const "Point"), Const "p"), App (Lam (Const "Point", Const "Point"), Const "p")) in
  assert (isDefEq env lctx (inferType env lctx term) (Sort 1));

  (* f: Point -> (fun a => Type) p *)
  (* (reduces to f: Point -> Type) *)
  Hashtbl.add env "f" (Forall (Const "Point", App (Lam (Const "Point", Sort 1), Const "p")));
  (* f p -> Point should not fail *)
  let term = Forall(App (Const "f", Const "p"), Const "Point") in
  assert (isDefEq env lctx (inferType env lctx term) (Sort 1));
  let term = Forall(Const "Point", App (Const "f", Const "p")) in
  assert (isDefEq env lctx (inferType env lctx term) (Sort 1));
  let term = Forall(App (Const "f", Const "p"), App (Const "f", Const "p")) in
  assert (isDefEq env lctx (inferType env lctx term) (Sort 1))

let () =
  (* Taken from https://stackoverflow.com/questions/65868770/lack-of-information-when-ocaml-crashes#comment128358969_65873074,
  turns on stack traces *)
  record_backtrace true;

  (* try *)
  test_kernel_reduce ();
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
  test_len_sanity ();
  test_len_app ();
  test_eq_symm ();
  (* with E_elab.Error.ElabError x ->
    print_endline ("Elaboration error: " ^ (E_elab.Error.pp_exn (E_elab.Elab.create ()) x)); *)

  print_endline "All inferType tests passed."
