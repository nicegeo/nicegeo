(* Tests for inferType with stack-based local context *)
open Kernel
open Term
open Infer
open Exceptions

(* For backwards compatibility during exception refactoring *)
let try_infer env localCtx t = inferType env localCtx t

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
  Alcotest.check' Testable.term ~msg:"Point is of Sort 1" ~actual:ty ~expected:(Sort 1);

  let ty_line = try_infer env (Hashtbl.create 0) (Const "Line") in
  Alcotest.check'
    Testable.term
    ~msg:"Line is of Sort 1"
    ~actual:ty_line
    ~expected:(Sort 1)

let test_fvar_lookup () =
  let env = mk_env () in
  let local_ctx = Hashtbl.create 16 in
  Hashtbl.add local_ctx "p1" (Const "Point");

  let ty = try_infer env local_ctx (Fvar "p1") in
  Alcotest.check'
    Testable.term
    ~msg:"p1 is of type Point"
    ~actual:ty
    ~expected:(Const "Point")

let test_fvar_unknown_fails () =
  let env = mk_env () in

  Alcotest.match_raises
    "unknown free variable should raise"
    (fun exn ->
      match exn with
      | TypeError { err_kind = UnknownFreeVarError _; _ } -> true
      | _ -> false)
    (fun () -> ignore (try_infer env (Hashtbl.create 0) (Fvar "nonexistent")))

let test_const_unknown_fails () =
  let env = mk_env () in

  Alcotest.match_raises
    "unknown constant should raise"
    (fun exn ->
      match exn with
      | TypeError { err_kind = UnknownConstError _; _ } -> true
      | _ -> false)
    (fun () -> ignore (try_infer env (Hashtbl.create 0) (Const "Unknown")))

let path_to_env = "../../../../synthetic/env.txt"

let test_empty_constants () =
  (* Empty and Empty.elim live in the axioms env *)
  let env = Elab.Interface.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in

  (* Empty : Type (i.e. Sort 1) *)
  let empty_ty = try_infer env.kenv lctx (Const "Empty") in
  Alcotest.check'
    Testable.term
    ~msg:"Empty is of Sort 1"
    ~actual:empty_ty
    ~expected:(Sort 1);

  (* Empty.elim : (C : Type) -> Empty -> C *)
  let elim_ty = try_infer env.kenv lctx (Const "Empty.elim") in
  Alcotest.check'
    Testable.term
    ~msg:"Empty.elim has correct type"
    ~actual:elim_ty
    ~expected:(Forall (Sort 1, Forall (Const "Empty", Bvar 1)))

let test_and_constants () =
  let env = Elab.Interface.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in
  (* And : (A : Prop) -> (B : Prop) -> Prop *)
  let and_ty = try_infer env.kenv lctx (Const "And") in
  Alcotest.check'
    Testable.term
    ~msg:"And has correct type"
    ~actual:and_ty
    ~expected:(Forall (Sort 0, Forall (Sort 0, Sort 0)));

  (* And.intro : (A : Prop) -> (B : Prop) -> (a : A) -> (b : B) -> And A B *)
  let intro_ty = try_infer env.kenv lctx (Const "And.intro") in
  Alcotest.check'
    Testable.term
    ~msg:"And.intro has correct type"
    ~actual:intro_ty
    ~expected:
      (Forall
         ( Sort 0,
           Forall
             ( Sort 0,
               Forall (Bvar 1, Forall (Bvar 1, App (App (Const "And", Bvar 3), Bvar 2)))
             ) ));

  (* And.elim : (A : Prop) -> (B : Prop) -> (C : Prop) -> (f : A -> B -> C) -> (h : And A B) -> C *)
  let elim_ty = try_infer env.kenv lctx (Const "And.elim") in
  Alcotest.check'
    Testable.term
    ~msg:"And.elim has correct type"
    ~actual:elim_ty
    ~expected:
      (Forall
         ( Sort 0,
           Forall
             ( Sort 0,
               Forall
                 ( Sort 0,
                   Forall
                     ( Forall (Bvar 2, Forall (Bvar 2, Bvar 2)),
                       Forall (App (App (Const "And", Bvar 3), Bvar 2), Bvar 2) ) ) ) ))

let test_infer_function_type () =
  let env = mk_env () in

  (* environment used in test contains a variable "p" with type Point *)
  let const_func = Lam (Const "Point", Const "p") in
  Alcotest.check'
    Testable.term
    ~msg:"const_func has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) const_func)
    ~expected:(Forall (Const "Point", Const "Point"));

  let identity_func = Lam (Const "Point", Bvar 0) in
  Alcotest.check'
    Testable.term
    ~msg:"identity_func has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) identity_func)
    ~expected:(Forall (Const "Point", Const "Point"));

  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  Alcotest.check'
    Testable.term
    ~msg:"generic_func has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) generic_func)
    ~expected:(Forall (Sort 1, Forall (Bvar 0, Bvar 1)))

let test_infer_forall () =
  let env = mk_env () in

  (* functions Point -> Point should be Type *)
  let forall_term = Forall (Const "Point", Const "Point") in
  Alcotest.check'
    Testable.term
    ~msg:"forall_term has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) forall_term)
    ~expected:(Sort 1);

  (* fun T: Type => (fun (t: T) => t) *)
  let generic_func = Lam (Sort 1, Lam (Bvar 0, Bvar 0)) in
  let generic_func_type = try_infer env (Hashtbl.create 0) generic_func in
  Alcotest.check'
    Testable.term
    ~msg:"generic_func has correct type"
    ~actual:generic_func_type
    ~expected:(Forall (Sort 1, Forall (Bvar 0, Bvar 1)));

  (* (T: Type) -> (T -> T) should be Type 1 (= Sort 2) *)
  Alcotest.check'
    Testable.term
    ~msg:"generic_func_type has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) generic_func_type)
    ~expected:(Sort 2);

  (* predicate *)
  let predicate = Forall (Const "Point", Sort 0) in
  Hashtbl.add env "IsRed" predicate;
  (* for all points p, p isRed -> p isRed *)
  let pred_forall =
    Forall
      (Const "Point", Forall (App (Const "IsRed", Bvar 0), App (Const "IsRed", Bvar 1)))
  in
  (* the forall statement is a Prop by impredicativity *)
  Alcotest.check'
    Testable.term
    ~msg:"pred_forall has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) pred_forall)
    ~expected:(Sort 0);

  let bigger_pred_forall = Forall (Sort 67, App (Const "IsRed", Const "p")) in
  Alcotest.check'
    Testable.term
    ~msg:"bigger_pred_forall has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) bigger_pred_forall)
    ~expected:(Sort 0);

  (* not a prop, something like fun (p: Point) => p=p like what you might see as a motive in eliminators *)
  let motive = Forall (Const "Point", Sort 0) in
  (* (Point -> Prop) : Type *)
  Alcotest.check'
    Testable.term
    ~msg:"motive has correct type"
    ~actual:(try_infer env (Hashtbl.create 0) motive)
    ~expected:(Sort 1);

  (* failure cases *)
  let return_type_not_sort = Forall (Const "Point", Const "p") in
  Alcotest.match_raises
    "return type not sort should raise"
    (fun exn ->
      match exn with TypeError { err_kind = ForallSortError _; _ } -> true | _ -> false)
    (fun () -> ignore (try_infer env (Hashtbl.create 0) return_type_not_sort));

  let domain_type_not_sort = Forall (Const "p", App (Const "IsRed", Const "p")) in
  Alcotest.match_raises
    "domain type not sort should raise"
    (fun exn ->
      match exn with TypeError { err_kind = ForallSortError _; _ } -> true | _ -> false)
    (fun () -> ignore (try_infer env (Hashtbl.create 0) domain_type_not_sort));

  let domain_and_return_type_not_sort = Forall (Const "p", Const "p") in
  Alcotest.match_raises
    "domain and return type not sort should raise"
    (fun exn ->
      match exn with TypeError { err_kind = ForallSortError _; _ } -> true | _ -> false)
    (fun () -> ignore (try_infer env (Hashtbl.create 0) domain_and_return_type_not_sort))

let test_infer_function_application () =
  let env = mk_env () in

  (* TODO: try testing case where return type is computed from argument? *)
  let local_ctx = Hashtbl.create 16 in
  Hashtbl.add local_ctx "p1" (Const "Point");

  let const_func_app = App (Lam (Const "Point", Const "p"), Fvar "p1") in
  Alcotest.check'
    Testable.term
    ~msg:"const_func_app has correct type"
    ~actual:(try_infer env local_ctx const_func_app)
    ~expected:(Const "Point");

  Hashtbl.clear local_ctx;
  Hashtbl.add local_ctx "l1" (Const "Line");

  Alcotest.match_raises
    "applying non-function should raise"
    (fun exn ->
      match exn with
      | TypeError { err_kind = UnknownFreeVarError _; _ } -> true
      | _ -> false)
    (fun () -> ignore (try_infer env local_ctx const_func_app));

  Hashtbl.clear local_ctx;

  let identity_func_app = App (Lam (Const "Point", Bvar 0), Const "p") in
  Alcotest.check'
    Testable.term
    ~msg:"identity_func_app has correct type"
    ~actual:(try_infer env local_ctx identity_func_app)
    ~expected:(Const "Point");

  let application_with_non_function = App (Const "p", Const "l") in
  Alcotest.match_raises
    "applying non-function should raise"
    (fun exn ->
      match exn with TypeError { err_kind = AppNonFuncError; _ } -> true | _ -> false)
    (fun () -> ignore (try_infer env local_ctx application_with_non_function));

  (* TODO: should Point be a Sort 0 or a Sort 1? *)
  (* Corresponds to the expression `(fun (A: Type) -> fun (x: A) -> x) Point` which
is equivalent to `fun (x: Point) -> x`, so we'd expect a type of `Point => Point` *)
  let generic_func_app = App (Lam (Sort 1, Lam (Bvar 0, Bvar 0)), Const "Point") in
  Alcotest.check'
    Testable.term
    ~msg:"generic_func_app has correct type"
    ~actual:(try_infer env local_ctx generic_func_app)
    ~expected:(Forall (Const "Point", Const "Point"))

let test_subst_bvar () =
  let open Internals in
  Alcotest.check'
    Testable.term
    ~msg:"no bvars"
    ~actual:(subst_bvar (Const "Point") 0 (Const "p"))
    ~expected:(Const "Point");

  Alcotest.check'
    Testable.term
    ~msg:"correct index"
    ~actual:(subst_bvar (Bvar 0) 0 (Const "p"))
    ~expected:(Const "p");

  Alcotest.check'
    Testable.term
    ~msg:"wrong index"
    ~actual:(subst_bvar (Bvar 0) 1 (Const "l"))
    ~expected:(Bvar 0);

  Alcotest.check'
    Testable.term
    ~msg:"substitute with bvar"
    ~actual:(subst_bvar (Bvar 0) 0 (Bvar 5))
    ~expected:(Bvar 5);

  (* The inner Bvar 0 refers to the argument to the Lam, so Bvar 0 for the topmost
  expression is Bvar 1 from the point of view of the inner expression *)
  Alcotest.check'
    Testable.term
    ~msg:"lambda argument but not inner bvar"
    ~actual:(subst_bvar (Lam (Bvar 0, Bvar 0)) 0 (Const "Point"))
    ~expected:(Lam (Const "Point", Bvar 0));

  Alcotest.check'
    Testable.term
    ~msg:"lambda argument and inner bvar"
    ~actual:(subst_bvar (Lam (Bvar 0, Bvar 1)) 0 (Const "Point"))
    ~expected:(Lam (Const "Point", Const "Point"));

  Alcotest.check'
    Testable.term
    ~msg:"lambda inner bvar unchanged"
    ~actual:(subst_bvar (Lam (Bvar 0, Bvar 1)) 1 (Const "Point"))
    ~expected:(Lam (Bvar 0, Bvar 1));

  (* Forall isn't really a function (in the sense that we can't apply it to an expression) 
  but the domain type does act as a bound variable similarly to a Lam, meaning that we
  need to recursively substitute in a Forall as well using the same rules*)
  Alcotest.check'
    Testable.term
    ~msg:"forall argument but not inner bvar"
    ~actual:(subst_bvar (Forall (Bvar 0, Bvar 0)) 0 (Sort 5))
    ~expected:(Forall (Sort 5, Bvar 0));

  Alcotest.check'
    Testable.term
    ~msg:"forall argument and inner bvar"
    ~actual:(subst_bvar (Forall (Bvar 0, Bvar 1)) 0 (Sort 5))
    ~expected:(Forall (Sort 5, Sort 5));

  Alcotest.check'
    Testable.term
    ~msg:"forall inner bvar unchanged"
    ~actual:(subst_bvar (Forall (Bvar 0, Bvar 1)) 1 (Sort 5))
    ~expected:(Forall (Bvar 0, Bvar 1))

let test_rebind_bvar () =
  let open Internals in
  Alcotest.check'
    Testable.term
    ~msg:"no bvars or fvars"
    ~actual:(rebind_bvar (Const "Point") 0 "p")
    ~expected:(Const "Point");

  Alcotest.check'
    Testable.term
    ~msg:"correct fvar name"
    ~actual:(rebind_bvar (Fvar "p") 0 "p")
    ~expected:(Bvar 0);

  Alcotest.check'
    Testable.term
    ~msg:"correct fvar name, index 1"
    ~actual:(rebind_bvar (Fvar "p") 1 "p")
    ~expected:(Bvar 1);

  Alcotest.check'
    Testable.term
    ~msg:"incorrect fvar name"
    ~actual:(rebind_bvar (Fvar "p") 0 "l")
    ~expected:(Fvar "p");

  Alcotest.check'
    Testable.term
    ~msg:"bvar unchanged"
    ~actual:(rebind_bvar (Bvar 0) 0 "p")
    ~expected:(Bvar 0);

  Alcotest.check'
    Testable.term
    ~msg:"bvar 5 unchanged"
    ~actual:(rebind_bvar (Bvar 5) 0 "p")
    ~expected:(Bvar 5);

  Alcotest.check'
    Testable.term
    ~msg:"bvar unchanged, index 5"
    ~actual:(rebind_bvar (Bvar 0) 5 "p")
    ~expected:(Bvar 0);

  Alcotest.check'
    Testable.term
    ~msg:"bvar 5 unchanged, index 5"
    ~actual:(rebind_bvar (Bvar 5) 5 "p")
    ~expected:(Bvar 5);

  Alcotest.check'
    Testable.term
    ~msg:"lambda argument"
    ~actual:(rebind_bvar (Lam (Fvar "Point", Bvar 0)) 0 "Point")
    ~expected:(Lam (Bvar 0, Bvar 0));

  Alcotest.check'
    Testable.term
    ~msg:"lambda argument and matching inner fvar"
    ~actual:(rebind_bvar (Lam (Fvar "Point", Fvar "Point")) 0 "Point")
    ~expected:(Lam (Bvar 0, Bvar 1));

  Alcotest.check'
    Testable.term
    ~msg:"lambda argument and not inner fvar"
    ~actual:(rebind_bvar (Lam (Fvar "Point", Fvar "Line")) 0 "Point")
    ~expected:(Lam (Bvar 0, Fvar "Line"));

  Alcotest.check'
    Testable.term
    ~msg:"bvar unchanged in lambda"
    ~actual:(rebind_bvar (Lam (Bvar 0, Bvar 1)) 1 "Point")
    ~expected:(Lam (Bvar 0, Bvar 1))

let test_eq_symm () =
  let application_multiple_arguments (func : term) (args : term list) : term =
    List.fold_left
      (fun application_so_far first_arg -> App (application_so_far, first_arg))
      func
      args
  in
  (* Confirm our helper function does what it should *)
  Alcotest.check'
    Testable.term
    ~msg:"application_multiple_arguments works"
    ~actual:
      (application_multiple_arguments (Const "f") [ Const "a"; Const "b"; Const "c" ])
    ~expected:(App (App (App (Const "f", Const "a"), Const "b"), Const "c"));

  let eq ty a b = App (App (App (Const "Eq", ty), a), b) in

  let env = Elab.Interface.create_with_env_path path_to_env in
  let local_ctx = Hashtbl.create 16 in

  let eq_symm_type =
    Forall
      ( Sort 1,
        (* A: Type *)
        Forall
          ( Bvar 0,
            (* a: A *)
            Forall
              ( Bvar 1,
                (* b: A *)
                Forall
                  ( eq (Bvar 2) (Bvar 1) (Bvar 0),
                    (* Eq a b *)
                    eq (Bvar 3) (Bvar 1) (Bvar 2)
                    (* Eq b a *) ) ) ) )
  in
  Alcotest.check'
    Testable.term
    ~msg:"eq_symm_type has correct type"
    ~actual:(try_infer env.kenv local_ctx eq_symm_type)
    ~expected:(Sort 0);

  (* make sure this is actually a Prop *)
  let eq_symm_term =
    Lam
      ( Sort 1,
        (* A: Type *)
        Lam
          ( Bvar 0,
            (* a: A *)
            Lam
              ( Bvar 1,
                (* b: A *)
                Lam
                  ( eq (Bvar 2) (Bvar 1) (Bvar 0),
                    (* eq_ab: Eq a b *)
                    application_multiple_arguments
                      (Const "Eq.elim")
                      [
                        Bvar 3;
                        (* A: Type *)
                        Bvar 2;
                        (* a: A *)
                        Lam (Bvar 3, eq (Bvar 4) (Bvar 0) (Bvar 3));
                        (* motive: A -> Prop *)
                        App (App (Const "Eq.intro", Bvar 3), Bvar 2);
                        (* refl: motive a *)
                        Bvar 1;
                        (* b: A *)
                        Bvar 0 (* eq_ab: Eq a b *);
                      ] ) ) ) )
  in
  let inferred_type = try_infer env.kenv local_ctx eq_symm_term in
  (* check that eq_symm_term is definitionally equal to the forall statement we expect *)
  Alcotest.check'
    (Testable.termDefEq env.kenv local_ctx)
    ~msg:"eq_symm_term has correct type"
    ~actual:inferred_type
    ~expected:eq_symm_type

(* These two tests are made by AI so can remove or change them completely if wanted *)
let test_len_sanity () =
  let env = Elab.Interface.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in

  (* Base types are Sort 1 *)
  Alcotest.check'
    Testable.term
    ~msg:"Measure is of Sort 1"
    ~actual:(try_infer env.kenv lctx (Const "Measure"))
    ~expected:(Sort 1);

  Alcotest.check'
    Testable.term
    ~msg:"Point is of Sort 1"
    ~actual:(try_infer env.kenv lctx (Const "Point"))
    ~expected:(Sort 1);

  (* Zero is an element of Measure *)
  Alcotest.check'
    Testable.term
    ~msg:"Zero is of type Measure"
    ~actual:(try_infer env.kenv lctx (Const "Zero"))
    ~expected:(Const "Measure");

  (* Lt and Add have the right top-level shape *)
  Alcotest.check'
    Testable.term
    ~msg:"Lt has correct type"
    ~actual:(try_infer env.kenv lctx (Const "Lt"))
    ~expected:(Forall (Const "Measure", Forall (Const "Measure", Sort 0)));

  Alcotest.check'
    Testable.term
    ~msg:"Add has correct type"
    ~actual:(try_infer env.kenv lctx (Const "Add"))
    ~expected:(Forall (Const "Measure", Forall (Const "Measure", Const "Measure")));

  (* AddZero is exact enough to check de Bruijn encoding *)
  let inferred = try_infer env.kenv lctx (Const "AddZero") in
  let expected =
    Forall
      ( Const "Measure",
        App
          ( App
              ( App (Const "Eq", Const "Measure"),
                App (App (Const "Add", Bvar 0), Const "Zero") ),
            Bvar 0 ) )
  in
  Alcotest.check'
    (Testable.termDefEq env.kenv lctx)
    ~msg:"AddZero has correct type"
    ~actual:inferred
    ~expected

let test_len_app () =
  let env = Elab.Interface.create_with_env_path path_to_env in
  let lctx = Hashtbl.create 16 in

  (* Lt Zero Zero : Prop *)
  Alcotest.check'
    Testable.term
    ~msg:"Lt Zero Zero is of type Prop"
    ~actual:(try_infer env.kenv lctx (App (App (Const "Lt", Const "Zero"), Const "Zero")))
    ~expected:(Sort 0);

  (* Add Zero Zero : Measure *)
  Alcotest.check'
    Testable.term
    ~msg:"Add Zero Zero is of type Measure"
    ~actual:
      (try_infer env.kenv lctx (App (App (Const "Add", Const "Zero"), Const "Zero")))
    ~expected:(Const "Measure");

  (* LtTrans applied to 3 Measure args gives Lt a b -> Lt b c -> Lt a c *)
  Hashtbl.add lctx "a" (Const "Measure");
  Hashtbl.add lctx "b" (Const "Measure");
  Hashtbl.add lctx "c" (Const "Measure");

  Alcotest.check'
    Testable.term
    ~msg:"LtTrans has correct type"
    ~actual:
      (try_infer
         env.kenv
         lctx
         (App (App (App (Const "LtTrans", Fvar "a"), Fvar "b"), Fvar "c")))
    ~expected:
      (Forall
         ( App (App (Const "Lt", Fvar "a"), Fvar "b"),
           Forall
             ( App (App (Const "Lt", Fvar "b"), Fvar "c"),
               App (App (Const "Lt", Fvar "a"), Fvar "c") ) ));

  (* Type mismatch: Lt applied to a Point should fail *)
  Hashtbl.add lctx "p" (Const "Point");
  Alcotest.match_raises
    "Lt applied to a Point should raise"
    (fun exn -> match exn with TypeError _ -> true | _ -> false)
    (fun () -> ignore (try_infer env.kenv lctx (App (Const "Lt", Fvar "p"))))

let test_kernel_reduce () =
  (* (fun (p1: Point) => (fun (p2: Point) => p2)) p) l *)
  (* should be reduced to (fun (p2: Point) => p2) l then to l *)
  let env = mk_env () in
  let lctx = Hashtbl.create 16 in

  let term =
    App (App (Lam (Const "Point", Lam (Const "Point", Bvar 0)), Const "p"), Const "l")
  in
  Alcotest.check'
    Testable.term
    ~msg:"application to nested lambdas"
    ~actual:(reduce env lctx term)
    ~expected:(Const "l");

  (* fun (x: (fun a => Point) p) => x is well-typed and should not fail inference *)
  (* (reduces to fun (x: Point) => x) *)
  let term = Lam (App (Lam (Const "Point", Const "Point"), Const "p"), Bvar 0) in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application in parameter is well-typed"
    ~actual:(inferType env lctx term)
    ~expected:(Forall (Const "Point", Const "Point"));

  (* (fun a => Point) p -> Point is well-typed and should not fail inference *)
  (* (reduces to Point -> Point) *)
  let term =
    Forall (App (Lam (Const "Point", Const "Point"), Const "p"), Const "Point")
  in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application in function input type is well-typed"
    ~actual:(inferType env lctx term)
    ~expected:(Sort 1);

  (* Point -> (fun a => Point) p *)
  let term =
    Forall (Const "Point", App (Lam (Const "Point", Const "Point"), Const "p"))
  in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application in function output type is well-typed"
    ~actual:(inferType env lctx term)
    ~expected:(Sort 1);

  (* (fun a => Point) p -> (fun a => Point) p *)
  let term =
    Forall
      ( App (Lam (Const "Point", Const "Point"), Const "p"),
        App (Lam (Const "Point", Const "Point"), Const "p") )
  in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application in input and output type is well-typed"
    ~actual:(inferType env lctx term)
    ~expected:(Sort 1);

  (* f: Point -> (fun a => Type) p *)
  (* (reduces to f: Point -> Type) *)
  Hashtbl.add
    env
    "f"
    (Forall (Const "Point", App (Lam (Const "Point", Sort 1), Const "p")));

  (* f p -> Point should not fail *)
  let term = Forall (App (Const "f", Const "p"), Const "Point") in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application with defined const in input type"
    ~actual:(inferType env lctx term)
    ~expected:(Sort 1);

  let term = Forall (Const "Point", App (Const "f", Const "p")) in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application with defined const in output type"
    ~actual:(inferType env lctx term)
    ~expected:(Sort 1);

  let term = Forall (App (Const "f", Const "p"), App (Const "f", Const "p")) in
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application with defined const in both input and output type"
    ~actual:(inferType env lctx term)
    ~expected:(Sort 1);

  (* g: (fun p => (Point -> Point)) p *)
  (* (reduces to g: Point -> Point) *)
  Hashtbl.add
    env
    "g"
    (App (Lam (Const "Point", Forall (Const "Point", Const "Point")), Const "p"));

  (* g p should not fail *)
  Alcotest.check'
    (Testable.termDefEq env lctx)
    ~msg:"application in function type is well-typed"
    ~actual:(inferType env lctx (App (Const "g", Const "p")))
    ~expected:(Const "Point")

let suite =
  let open Alcotest in
  ( "kernel",
    [
      test_case "Constant lookup" `Quick test_const_lookup;
      test_case "Free variable lookup" `Quick test_fvar_lookup;
      test_case "Unknown free variable should raise" `Quick test_fvar_unknown_fails;
      test_case "Unknown constant should raise" `Quick test_const_unknown_fails;
      test_case "Empty constants" `Quick test_empty_constants;
      test_case "And constants" `Quick test_and_constants;
      test_case "Infer function type" `Quick test_infer_function_type;
      test_case "Infer forall" `Quick test_infer_forall;
      test_case "Infer function application" `Quick test_infer_function_application;
      test_case "Substitution of bound variables" `Quick test_subst_bvar;
      test_case "Rebinding bound variables" `Quick test_rebind_bvar;
      test_case "Symmetry of equality" `Quick test_eq_symm;
      test_case "Measure sanity checks" `Quick test_len_sanity;
      test_case "Measure application" `Quick test_len_app;
      test_case "Kernel reduction" `Quick test_kernel_reduce;
    ] )
