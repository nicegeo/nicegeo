let rec collect_bound_names (tm : Elab.Term.term) : string list =
  let open Elab.Term in
  match tm.inner with
  | Fun (name, ty, body) ->
      let ty_names = collect_bound_names ty in
      let body_names = collect_bound_names body in
      ((match name with Some n -> n | None -> "") :: ty_names) @ body_names
  | Arrow (name, ty, ret) ->
      let ty_names = collect_bound_names ty in
      let ret_names = collect_bound_names ret in
      ((match name with Some n -> n | None -> "") :: ty_names) @ ret_names
  | App (f, arg) -> collect_bound_names f @ collect_bound_names arg
  | Name _ | Bvar _ | Fvar _ | Hole _ | Sort _ -> []

let kterm_to_repr (term : Kernel.Term.term) (bound_names : string list) =
  let open Kernel.Term in
  let rec kterm_to_repr_helper (term : term) (indent : int) (bound_names : string list)
      (bvars : string list) =
    let indent_str = String.make (indent * 2) ' ' in
    match term with
    | Const s -> (Printf.sprintf "Const \"%s\"" s, bound_names)
    | Bvar n ->
        ( Printf.sprintf
            "Bvar %d %s"
            n
            (if List.nth bvars n = "" then "" else "(* " ^ List.nth bvars n ^ " *)"),
          bound_names )
    | Lam (ty, body) -> (
        match bound_names with
        | name :: rest_names ->
            let ty_repr, next_bound_names =
              kterm_to_repr_helper ty indent rest_names bvars
            in
            let body_repr, next_next_bound_names =
              kterm_to_repr_helper body (indent + 1) next_bound_names (name :: bvars)
            in
            ( Printf.sprintf
                "Lam (%s%s,\n%s  %s\n%s)"
                (if name = "" then "" else "(* " ^ name ^ " : *)")
                ty_repr
                indent_str
                body_repr
                indent_str,
              next_next_bound_names )
        | [] -> failwith "Not enough bound names provided in kterm_to_repr input")
    | Forall (ty, ret) -> (
        match bound_names with
        | name :: rest_names ->
            let ty_repr, next_bound_names =
              kterm_to_repr_helper ty indent rest_names bvars
            in
            let ret_repr, next_next_bound_names =
              kterm_to_repr_helper ret (indent + 1) next_bound_names (name :: bvars)
            in
            ( Printf.sprintf
                "Forall (%s%s,\n%s  %s\n%s)"
                (if name = "" then "" else "(* " ^ name ^ " : *)")
                ty_repr
                indent_str
                ret_repr
                indent_str,
              next_next_bound_names )
        | [] -> failwith "Not enough bound names provided in kterm_to_repr input")
    | App (f, arg) ->
        let f_repr, next_bound_names = kterm_to_repr_helper f indent bound_names bvars in
        let arg_repr, next_next_bound_names =
          kterm_to_repr_helper arg indent next_bound_names bvars
        in
        (Printf.sprintf "App (%s, %s)" f_repr arg_repr, next_next_bound_names)
    | Sort n -> (Printf.sprintf "Sort %d" n, bound_names)
    | Fvar _ -> failwith "fvar in kterm_to_repr input"
  in
  fst (kterm_to_repr_helper term 0 bound_names [])

(** These are the regression tests for the axioms in env.txt. If [dune runtest] yields
    errors here, inspect the diff to ensure that all changes in the kernel terms make
    sense. Assume changes in the term representation of the axioms are regressions unless
    you fully understand what the change represents.

    If the changes make sense and are intended behavior, run [dune promote] to update the
    regression tests.

    At the end of this test, there is a check that all definitions in the environment have
    been checked. If you see the [[%expect.unreachable]] at the end being replaced with a
    list of missing definitions, DO NOT PROMOTE. Instead, check that each of the missing
    definitions are indeed missing axioms, and then add a section like this for each:

    {[
      (* Name : Type *)
      show_kterm "Name";
      [%expect]
    ]}

    Running [dune runtest] again will fill in the expect with the kernel term
    representation. Ensure this representation is correct before promoting and pushing. *)

let%expect_test "Elaborate env.txt" =
  let env = Elab.Interface.create_with_env_path "../../../../../../synthetic/env.txt" in
  let kenv = Hashtbl.copy env.kenv in

  let show_kterm name =
    let term = (Hashtbl.find env.env name).ty in
    let bound_names = collect_bound_names term in
    let kterm = Hashtbl.find kenv name in
    let repr = kterm_to_repr kterm bound_names in
    print_endline repr;
    (* Delete entry from kenv so we can check this is empty at the end *)
    Hashtbl.remove kenv name
  in

  (* Empty : Type *)
  show_kterm "Empty";
  [%expect {| Sort 1 |}];

  (* Empty.elim : (C: Type) -> Empty -> C *)
  show_kterm "Empty.elim";
  [%expect
    {|
    Forall ((* C : *)Sort 1,
      Forall (Const "Empty",
        Bvar 1 (* C *)
      )
    )
    |}];

  (* False : Prop *)
  show_kterm "False";
  [%expect {| Sort 0 |}];

  (* False.elim : (P: Prop) -> False -> P *)
  show_kterm "False.elim";
  [%expect
    {|
    Forall ((* P : *)Sort 0,
      Forall (Const "False",
        Bvar 1 (* P *)
      )
    )
    |}];

  (* True : Prop *)
  show_kterm "True";
  [%expect {| Sort 0 |}];

  (* True.intro : True *)
  show_kterm "True.intro";
  [%expect {| Const "True" |}];

  (* Exists : (A: Type) -> (A -> Prop) -> Prop *)
  show_kterm "Exists";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall (Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Sort 0
      )
    )
    |}];

  (* Exists.intro : (A: Type) -> (p: A -> Prop) -> (a: A) -> (h: p a) -> Exists A p *)
  show_kterm "Exists.intro";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* p : *)Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Forall ((* a : *)Bvar 1 (* A *),
          Forall ((* h : *)App (Bvar 1 (* p *), Bvar 0 (* a *)),
            App (App (Const "Exists", Bvar 3 (* A *)), Bvar 2 (* p *))
          )
        )
      )
    )
    |}];

  (* Exists.elim : (A: Type) -> (p: A -> Prop) -> (b: Prop) -> 
      (e: Exists A p) -> ((a: A) -> p a -> b) -> b *)
  show_kterm "Exists.elim";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* p : *)Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Forall ((* b : *)Sort 0,
          Forall ((* e : *)App (App (Const "Exists", Bvar 2 (* A *)), Bvar 1 (* p *)),
            Forall (Forall ((* a : *)Bvar 3 (* A *),
              Forall (App (Bvar 3 (* p *), Bvar 0 (* a *)),
                Bvar 3 (* b *)
              )
            ),
              Bvar 2 (* b *)
            )
          )
        )
      )
    )
    |}];

  (* Forall : (A: Type) -> (A -> Prop) -> Prop *)
  show_kterm "Forall";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall (Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Sort 0
      )
    )
    |}];

  (* Forall.intro : (A: Type) -> (p: A -> Prop) ->
      ((a: A) -> p a) -> Forall A p *)
  show_kterm "Forall.intro";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* p : *)Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Forall (Forall ((* a : *)Bvar 1 (* A *),
          App (Bvar 1 (* p *), Bvar 0 (* a *))
        ),
          App (App (Const "Forall", Bvar 2 (* A *)), Bvar 1 (* p *))
        )
      )
    )
    |}];

  (* Forall.elim : (A: Type) -> (p: A -> Prop) ->
      Forall A p -> (a: A) -> p a *)
  show_kterm "Forall.elim";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* p : *)Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Forall (App (App (Const "Forall", Bvar 1 (* A *)), Bvar 0 (* p *)),
          Forall ((* a : *)Bvar 2 (* A *),
            App (Bvar 2 (* p *), Bvar 0 (* a *))
          )
        )
      )
    )
    |}];

  (* And : Prop -> Prop -> Prop *)
  show_kterm "And";
  [%expect
    {|
    Forall (Sort 0,
      Forall (Sort 0,
        Sort 0
      )
    )
    |}];

  (* And.intro : (A : Prop) -> (B : Prop) -> (a : A) -> (b : B) -> And A B *)
  show_kterm "And.intro";
  [%expect
    {|
    Forall ((* A : *)Sort 0,
      Forall ((* B : *)Sort 0,
        Forall ((* a : *)Bvar 1 (* A *),
          Forall ((* b : *)Bvar 1 (* B *),
            App (App (Const "And", Bvar 3 (* A *)), Bvar 2 (* B *))
          )
        )
      )
    )
    |}];

  (* And.elim : (A : Prop) -> (B : Prop) -> (C : Prop) ->
      (f : A -> B -> C) -> And A B -> C *)
  show_kterm "And.elim";
  [%expect
    {|
    Forall ((* A : *)Sort 0,
      Forall ((* B : *)Sort 0,
        Forall ((* C : *)Sort 0,
          Forall ((* f : *)Forall (Bvar 2 (* A *),
            Forall (Bvar 2 (* B *),
              Bvar 2 (* C *)
            )
          ),
            Forall (App (App (Const "And", Bvar 3 (* A *)), Bvar 2 (* B *)),
              Bvar 2 (* C *)
            )
          )
        )
      )
    )
    |}];

  (* Or : Prop -> Prop -> Prop *)
  show_kterm "Or";
  [%expect
    {|
    Forall (Sort 0,
      Forall (Sort 0,
        Sort 0
      )
    )
    |}];

  (* Or.inl : (A : Prop) -> (B : Prop) -> A -> Or A B *)
  show_kterm "Or.inl";
  [%expect
    {|
    Forall ((* A : *)Sort 0,
      Forall ((* B : *)Sort 0,
        Forall (Bvar 1 (* A *),
          App (App (Const "Or", Bvar 2 (* A *)), Bvar 1 (* B *))
        )
      )
    )
    |}];

  (* Or.inr : (A : Prop) -> (B : Prop) -> B -> Or A B *)
  show_kterm "Or.inr";
  [%expect
    {|
    Forall ((* A : *)Sort 0,
      Forall ((* B : *)Sort 0,
        Forall (Bvar 0 (* B *),
          App (App (Const "Or", Bvar 2 (* A *)), Bvar 1 (* B *))
        )
      )
    )
    |}];

  (* Or.elim : (A : Prop) -> (B : Prop) -> (C : Prop) ->
      Or A B -> (A -> C) -> (B -> C) -> C *)
  show_kterm "Or.elim";
  [%expect
    {|
    Forall ((* A : *)Sort 0,
      Forall ((* B : *)Sort 0,
        Forall ((* C : *)Sort 0,
          Forall (App (App (Const "Or", Bvar 2 (* A *)), Bvar 1 (* B *)),
            Forall (Forall (Bvar 3 (* A *),
              Bvar 2 (* C *)
            ),
              Forall (Forall (Bvar 3 (* B *),
                Bvar 3 (* C *)
              ),
                Bvar 3 (* C *)
              )
            )
          )
        )
      )
    )
    |}];

  (* Not : Prop -> Prop *)
  show_kterm "Not";
  [%expect {|
    Forall (Sort 0,
      Sort 0
    )
    |}];

  (* Not.intro : (P : Prop) -> (P -> False) -> Not P *)
  show_kterm "Not.intro";
  [%expect
    {|
    Forall ((* P : *)Sort 0,
      Forall (Forall (Bvar 0 (* P *),
        Const "False"
      ),
        App (Const "Not", Bvar 1 (* P *))
      )
    )
    |}];

  (* Not.elim : (P : Prop) -> Not P -> P -> False *)
  show_kterm "Not.elim";
  [%expect
    {|
    Forall ((* P : *)Sort 0,
      Forall (App (Const "Not", Bvar 0 (* P *)),
        Forall (Bvar 1 (* P *),
          Const "False"
        )
      )
    )
    |}];

  (* Eq : (T: Type) -> T -> T -> Prop *)
  show_kterm "Eq";
  [%expect
    {|
    Forall ((* T : *)Sort 1,
      Forall (Bvar 0 (* T *),
        Forall (Bvar 1 (* T *),
          Sort 0
        )
      )
    )
    |}];

  (* Eq.intro : (T: Type) -> (t: T) -> Eq T t t *)
  show_kterm "Eq.intro";
  [%expect
    {|
    Forall ((* T : *)Sort 1,
      Forall ((* t : *)Bvar 0 (* T *),
        App (App (App (Const "Eq", Bvar 1 (* T *)), Bvar 0 (* t *)), Bvar 0 (* t *))
      )
    )
    |}];

  (* Eq.elim : (T: Type) -> (t: T) -> (motive : T -> Prop) -> (rfl: motive t) -> (t1: T) -> Eq T t t1 -> motive t1 *)
  show_kterm "Eq.elim";
  [%expect
    {|
    Forall ((* T : *)Sort 1,
      Forall ((* t : *)Bvar 0 (* T *),
        Forall ((* motive : *)Forall (Bvar 1 (* T *),
          Sort 0
        ),
          Forall ((* rfl : *)App (Bvar 0 (* motive *), Bvar 1 (* t *)),
            Forall ((* t1 : *)Bvar 3 (* T *),
              Forall (App (App (App (Const "Eq", Bvar 4 (* T *)), Bvar 3 (* t *)), Bvar 0 (* t1 *)),
                App (Bvar 3 (* motive *), Bvar 1 (* t1 *))
              )
            )
          )
        )
      )
    )
    |}];

  (* List : Type -> Type *)
  show_kterm "List";
  [%expect {|
    Forall (Sort 1,
      Sort 1
    )
    |}];

  (* List.nil : (A : Type) -> List A *)
  show_kterm "List.nil";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      App (Const "List", Bvar 0 (* A *))
    )
    |}];

  (* List.cons : (A : Type) -> A -> List A -> List A *)
  show_kterm "List.cons";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall (Bvar 0 (* A *),
        Forall (App (Const "List", Bvar 1 (* A *)),
          App (Const "List", Bvar 2 (* A *))
        )
      )
    )
    |}];

  (* List.mem : (A : Type) -> A -> List A -> Prop *)
  show_kterm "List.mem";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall (Bvar 0 (* A *),
        Forall (App (Const "List", Bvar 1 (* A *)),
          Sort 0
        )
      )
    )
    |}];

  (* List.not_mem_nil : (A : Type) -> (a : A) -> List.mem A a (List.nil A) -> False *)
  show_kterm "List.not_mem_nil";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* a : *)Bvar 0 (* A *),
        Forall (App (App (App (Const "List.mem", Bvar 1 (* A *)), Bvar 0 (* a *)), App (Const "List.nil", Bvar 1 (* A *))),
          Const "False"
        )
      )
    )
    |}];

  (* List.mem_cons : (A : Type) -> (a : A) -> (b : A) -> (L : List A) ->
    And (List.mem A a (List.cons A b L) -> Or (Eq A a b) (List.mem A a L))
        (Or (Eq A a b) (List.mem A a L) -> List.mem A a (List.cons A b L)) *)
  show_kterm "List.mem_cons";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* a : *)Bvar 0 (* A *),
        Forall ((* b : *)Bvar 1 (* A *),
          Forall ((* L : *)App (Const "List", Bvar 2 (* A *)),
            App (App (Const "And", Forall (App (App (App (Const "List.mem", Bvar 3 (* A *)), Bvar 2 (* a *)), App (App (App (Const "List.cons", Bvar 3 (* A *)), Bvar 1 (* b *)), Bvar 0 (* L *))),
              App (App (Const "Or", App (App (App (Const "Eq", Bvar 4 (* A *)), Bvar 3 (* a *)), Bvar 2 (* b *))), App (App (App (Const "List.mem", Bvar 4 (* A *)), Bvar 3 (* a *)), Bvar 1 (* L *)))
            )), Forall (App (App (Const "Or", App (App (App (Const "Eq", Bvar 3 (* A *)), Bvar 2 (* a *)), Bvar 1 (* b *))), App (App (App (Const "List.mem", Bvar 3 (* A *)), Bvar 2 (* a *)), Bvar 0 (* L *))),
              App (App (App (Const "List.mem", Bvar 4 (* A *)), Bvar 3 (* a *)), App (App (App (Const "List.cons", Bvar 4 (* A *)), Bvar 2 (* b *)), Bvar 1 (* L *)))
            ))
          )
        )
      )
    )
    |}];

  (* List.forall : (A : Type) -> (A -> Prop) -> List A -> Prop *)
  show_kterm "List.forall";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall (Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Forall (App (Const "List", Bvar 1 (* A *)),
          Sort 0
        )
      )
    )
    |}];

  (* List.forall_nil : (A : Type) -> (p : A -> Prop) -> List.forall A p (List.nil A) *)
  show_kterm "List.forall_nil";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* p : *)Forall (Bvar 0 (* A *),
        Sort 0
      ),
        App (App (App (Const "List.forall", Bvar 1 (* A *)), Bvar 0 (* p *)), App (Const "List.nil", Bvar 1 (* A *)))
      )
    )
    |}];

  (* List.forall_cons : (A : Type) -> (p : A -> Prop) -> (a : A) -> (L : List A) ->
    And (List.forall A p (List.cons A a L) -> And (p a) (List.forall A p L))
        (And (p a) (List.forall A p L) -> List.forall A p (List.cons A a L)) *)
  show_kterm "List.forall_cons";
  [%expect
    {|
    Forall ((* A : *)Sort 1,
      Forall ((* p : *)Forall (Bvar 0 (* A *),
        Sort 0
      ),
        Forall ((* a : *)Bvar 1 (* A *),
          Forall ((* L : *)App (Const "List", Bvar 2 (* A *)),
            App (App (Const "And", Forall (App (App (App (Const "List.forall", Bvar 3 (* A *)), Bvar 2 (* p *)), App (App (App (Const "List.cons", Bvar 3 (* A *)), Bvar 1 (* a *)), Bvar 0 (* L *))),
              App (App (Const "And", App (Bvar 3 (* p *), Bvar 2 (* a *))), App (App (App (Const "List.forall", Bvar 4 (* A *)), Bvar 3 (* p *)), Bvar 1 (* L *)))
            )), Forall (App (App (Const "And", App (Bvar 2 (* p *), Bvar 1 (* a *))), App (App (App (Const "List.forall", Bvar 3 (* A *)), Bvar 2 (* p *)), Bvar 0 (* L *))),
              App (App (App (Const "List.forall", Bvar 4 (* A *)), Bvar 3 (* p *)), App (App (App (Const "List.cons", Bvar 4 (* A *)), Bvar 2 (* a *)), Bvar 1 (* L *)))
            ))
          )
        )
      )
    )
    |}];

  (* Point : Type *)
  show_kterm "Point";
  [%expect {| Sort 1 |}];

  (* Line : Type *)
  show_kterm "Line";
  [%expect {| Sort 1 |}];

  (* Circle : Type *)
  show_kterm "Circle";
  [%expect {| Sort 1 |}];

  (* Measure : Type *)
  show_kterm "Measure";
  [%expect {| Sort 1 |}];

  (* Lt : Measure -> Measure -> Prop *)
  show_kterm "Lt";
  [%expect
    {|
    Forall (Const "Measure",
      Forall (Const "Measure",
        Sort 0
      )
    )
    |}];

  (* LtIrrefl : (a : Measure) -> (Lt a a -> False) *)
  show_kterm "LtIrrefl";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall (App (App (Const "Lt", Bvar 0 (* a *)), Bvar 0 (* a *)),
        Const "False"
      )
    )
    |}];

  (* LtTrans : (a: Measure) -> (b: Measure) -> (c: Measure) -> Lt a b -> Lt b c -> Lt a c *)
  show_kterm "LtTrans";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall ((* b : *)Const "Measure",
        Forall ((* c : *)Const "Measure",
          Forall (App (App (Const "Lt", Bvar 2 (* a *)), Bvar 1 (* b *)),
            Forall (App (App (Const "Lt", Bvar 2 (* b *)), Bvar 1 (* c *)),
              App (App (Const "Lt", Bvar 4 (* a *)), Bvar 2 (* c *))
            )
          )
        )
      )
    )
    |}];

  (* LtTricot : (a: Measure) -> (b: Measure) -> Or (Lt a b) (Or (Lt b a) (Eq Measure a b)) *)
  show_kterm "LtTricot";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall ((* b : *)Const "Measure",
        App (App (Const "Or", App (App (Const "Lt", Bvar 1 (* a *)), Bvar 0 (* b *))), App (App (Const "Or", App (App (Const "Lt", Bvar 0 (* b *)), Bvar 1 (* a *))), App (App (App (Const "Eq", Const "Measure"), Bvar 1 (* a *)), Bvar 0 (* b *))))
      )
    )
    |}];

  (* LtAntisymm : (a: Measure) -> (b: Measure) -> Lt a b -> Lt b a -> False *)
  show_kterm "LtAntisymm";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall ((* b : *)Const "Measure",
        Forall (App (App (Const "Lt", Bvar 1 (* a *)), Bvar 0 (* b *)),
          Forall (App (App (Const "Lt", Bvar 1 (* b *)), Bvar 2 (* a *)),
            Const "False"
          )
        )
      )
    )
    |}];

  (* Zero : Measure *)
  show_kterm "Zero";
  [%expect {| Const "Measure" |}];

  (* ZeroLeast : (a: Measure) -> Or (Lt Zero a) (Eq Measure Zero a) *)
  show_kterm "ZeroLeast";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      App (App (Const "Or", App (App (Const "Lt", Const "Zero"), Bvar 0 (* a *))), App (App (App (Const "Eq", Const "Measure"), Const "Zero"), Bvar 0 (* a *)))
    )
    |}];

  (* Add : Measure -> Measure -> Measure *)
  show_kterm "Add";
  [%expect
    {|
    Forall (Const "Measure",
      Forall (Const "Measure",
        Const "Measure"
      )
    )
    |}];

  (* AddComm : (a: Measure) -> (b: Measure) -> Eq Measure (Add a b) (Add b a) *)
  show_kterm "AddComm";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall ((* b : *)Const "Measure",
        App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", Bvar 1 (* a *)), Bvar 0 (* b *))), App (App (Const "Add", Bvar 0 (* b *)), Bvar 1 (* a *)))
      )
    )
    |}];

  (* AddAssoc : (a: Measure) -> (b: Measure) -> (c: Measure) -> Eq Measure (Add (Add a b) c) (Add a (Add b c)) *)
  show_kterm "AddAssoc";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall ((* b : *)Const "Measure",
        Forall ((* c : *)Const "Measure",
          App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (Const "Add", Bvar 2 (* a *)), Bvar 1 (* b *))), Bvar 0 (* c *))), App (App (Const "Add", Bvar 2 (* a *)), App (App (Const "Add", Bvar 1 (* b *)), Bvar 0 (* c *))))
        )
      )
    )
    |}];

  (* AddZero : (a: Measure) -> Eq Measure (Add a Zero) a *)
  show_kterm "AddZero";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", Bvar 0 (* a *)), Const "Zero")), Bvar 0 (* a *))
    )
    |}];

  (* LtAdd : (a: Measure) -> (b: Measure) -> (c: Measure) -> Lt a b -> Lt (Add a c) (Add b c) *)
  show_kterm "LtAdd";
  [%expect
    {|
    Forall ((* a : *)Const "Measure",
      Forall ((* b : *)Const "Measure",
        Forall ((* c : *)Const "Measure",
          Forall (App (App (Const "Lt", Bvar 2 (* a *)), Bvar 1 (* b *)),
            App (App (Const "Lt", App (App (Const "Add", Bvar 3 (* a *)), Bvar 1 (* c *))), App (App (Const "Add", Bvar 2 (* b *)), Bvar 1 (* c *)))
          )
        )
      )
    )
    |}];

  (* OnLine : Point -> Line -> Prop *)
  show_kterm "OnLine";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Line",
        Sort 0
      )
    )
    |}];

  (* SameSide : Point -> Point -> Line -> Prop *)
  show_kterm "SameSide";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Line",
          Sort 0
        )
      )
    )
    |}];

  (* Between : Point -> Point -> Point -> Prop *)
  show_kterm "Between";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Sort 0
        )
      )
    )
    |}];

  (* Length : (a: Point) -> (b: Point) -> Measure *)
  show_kterm "Length";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Const "Measure"
      )
    )
    |}];

  (* Angle : (a: Point) -> (b: Point) -> (c: Point) -> Measure *)
  show_kterm "Angle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Const "Measure"
        )
      )
    )
    |}];

  (* Area : (a: Point) -> (b: Point) -> (c: Point) -> Measure *)
  show_kterm "Area";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Const "Measure"
        )
      )
    )
    |}];

  (* OnCircle : Point -> Circle -> Prop *)
  show_kterm "OnCircle";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Circle",
        Sort 0
      )
    )
    |}];

  (* InCircle : Point -> Circle -> Prop *)
  show_kterm "InCircle";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Circle",
        Sort 0
      )
    )
    |}];

  (* CenterCircle : Point -> Circle -> Prop *)
  show_kterm "CenterCircle";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Circle",
        Sort 0
      )
    )
    |}];

  (* LinesInter : Line -> Line -> Prop *)
  show_kterm "LinesInter";
  [%expect
    {|
    Forall (Const "Line",
      Forall (Const "Line",
        Sort 0
      )
    )
    |}];

  (* LineCircleInter : Line -> Circle -> Prop *)
  show_kterm "LineCircleInter";
  [%expect
    {|
    Forall (Const "Line",
      Forall (Const "Circle",
        Sort 0
      )
    )
    |}];

  (* CirclesInter : Circle -> Circle -> Prop *)
  show_kterm "CirclesInter";
  [%expect
    {|
    Forall (Const "Circle",
      Forall (Const "Circle",
        Sort 0
      )
    )
    |}];

  (* RightAngle : Measure *)
  show_kterm "RightAngle";
  [%expect {| Const "Measure" |}];

  (* distinct_from : Point -> List Point -> List Line -> List Circle -> Prop *)
  show_kterm "distinct_from";
  [%expect
    {|
    Forall (Const "Point",
      Forall (App (Const "List", Const "Point"),
        Forall (App (Const "List", Const "Line"),
          Forall (App (Const "List", Const "Circle"),
            Sort 0
          )
        )
      )
    )
    |}];

  (* distinct_from.intro : (a : Point) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    (Not (List.mem Point a p_list)) ->
    (List.forall Line (fun (L : Line) => Not (OnLine a L)) l_list) ->
    (List.forall Circle (fun (aa : Circle) => Not (OnCircle a aa)) c_list) ->
    distinct_from a p_list l_list c_list *)
  show_kterm "distinct_from.intro";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* p_list : *)App (Const "List", Const "Point"),
        Forall ((* l_list : *)App (Const "List", Const "Line"),
          Forall ((* c_list : *)App (Const "List", Const "Circle"),
            Forall (App (Const "Not", App (App (App (Const "List.mem", Const "Point"), Bvar 3 (* a *)), Bvar 2 (* p_list *))),
              Forall (App (App (App (Const "List.forall", Const "Line"), Lam ((* L : *)Const "Line",
                App (Const "Not", App (App (Const "OnLine", Bvar 5 (* a *)), Bvar 0 (* L *)))
              )), Bvar 2 (* l_list *)),
                Forall (App (App (App (Const "List.forall", Const "Circle"), Lam ((* aa : *)Const "Circle",
                  App (Const "Not", App (App (Const "OnCircle", Bvar 6 (* a *)), Bvar 0 (* aa *)))
                )), Bvar 2 (* c_list *)),
                  App (App (App (App (Const "distinct_from", Bvar 6 (* a *)), Bvar 5 (* p_list *)), Bvar 4 (* l_list *)), Bvar 3 (* c_list *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* distinct_from.elim : (a : Point) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    distinct_from a p_list l_list c_list ->
    And (And (Not (List.mem Point a p_list)) (List.forall Line (fun (L : Line) => Not (OnLine a L)) l_list)) (List.forall Circle (fun (aa : Circle) => Not (OnCircle a aa)) c_list) *)
  show_kterm "distinct_from.elim";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* p_list : *)App (Const "List", Const "Point"),
        Forall ((* l_list : *)App (Const "List", Const "Line"),
          Forall ((* c_list : *)App (Const "List", Const "Circle"),
            Forall (App (App (App (App (Const "distinct_from", Bvar 3 (* a *)), Bvar 2 (* p_list *)), Bvar 1 (* l_list *)), Bvar 0 (* c_list *)),
              App (App (Const "And", App (App (Const "And", App (Const "Not", App (App (App (Const "List.mem", Const "Point"), Bvar 4 (* a *)), Bvar 3 (* p_list *)))), App (App (App (Const "List.forall", Const "Line"), Lam ((* L : *)Const "Line",
                App (Const "Not", App (App (Const "OnLine", Bvar 5 (* a *)), Bvar 0 (* L *)))
              )), Bvar 2 (* l_list *)))), App (App (App (Const "List.forall", Const "Circle"), Lam ((* aa : *)Const "Circle",
                App (Const "Not", App (App (Const "OnCircle", Bvar 5 (* a *)), Bvar 0 (* aa *)))
              )), Bvar 1 (* c_list *)))
            )
          )
        )
      )
    )
    |}];

  (* pt_exists :
    (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    Exists Point (fun (a : Point) => distinct_from a p_list l_list c_list) *)
  show_kterm "pt_exists";
  [%expect
    {|
    Forall ((* p_list : *)App (Const "List", Const "Point"),
      Forall ((* l_list : *)App (Const "List", Const "Line"),
        Forall ((* c_list : *)App (Const "List", Const "Circle"),
          App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
            App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 3 (* p_list *)), Bvar 2 (* l_list *)), Bvar 1 (* c_list *))
          ))
        )
      )
    )
    |}];

  (* pt_on_line :
    (L : Line) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    (Not (List.mem Line L l_list)) ->
    Exists Point (fun (a : Point) => And (OnLine a L) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_on_line";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* p_list : *)App (Const "List", Const "Point"),
        Forall ((* l_list : *)App (Const "List", Const "Line"),
          Forall ((* c_list : *)App (Const "List", Const "Circle"),
            Forall (App (Const "Not", App (App (App (Const "List.mem", Const "Line"), Bvar 3 (* L *)), Bvar 1 (* l_list *))),
              App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 5 (* L *))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 4 (* p_list *)), Bvar 3 (* l_list *)), Bvar 2 (* c_list *)))
              ))
            )
          )
        )
      )
    )
    |}];

  (* pt_between_on_line :
    (L : Line) -> (b : Point) -> (c : Point) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    OnLine b L -> OnLine c L -> (Eq Point b c -> False) -> (Not (List.mem Line L l_list)) ->
    Exists Point (fun (a : Point) =>
      And (And (OnLine a L) (Between b a c)) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_between_on_line";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* p_list : *)App (Const "List", Const "Point"),
            Forall ((* l_list : *)App (Const "List", Const "Line"),
              Forall ((* c_list : *)App (Const "List", Const "Circle"),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 5 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 6 (* L *)),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 6 (* b *)), Bvar 5 (* c *)),
                      Const "False"
                    ),
                      Forall (App (Const "Not", App (App (App (Const "List.mem", Const "Line"), Bvar 8 (* L *)), Bvar 4 (* l_list *))),
                        App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                          App (App (Const "And", App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 10 (* L *))), App (App (App (Const "Between", Bvar 9 (* b *)), Bvar 0 (* a *)), Bvar 8 (* c *)))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 7 (* p_list *)), Bvar 6 (* l_list *)), Bvar 5 (* c_list *)))
                        ))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_extension_on_line :
    (L : Line) -> (b : Point) -> (c : Point) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    OnLine b L -> OnLine c L -> (Eq Point b c -> False) -> (Not (List.mem Line L l_list)) ->
    Exists Point (fun (a : Point) =>
      And (And (OnLine a L) (Between b c a)) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_extension_on_line";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* p_list : *)App (Const "List", Const "Point"),
            Forall ((* l_list : *)App (Const "List", Const "Line"),
              Forall ((* c_list : *)App (Const "List", Const "Circle"),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 5 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 6 (* L *)),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 6 (* b *)), Bvar 5 (* c *)),
                      Const "False"
                    ),
                      Forall (App (Const "Not", App (App (App (Const "List.mem", Const "Line"), Bvar 8 (* L *)), Bvar 4 (* l_list *))),
                        App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                          App (App (Const "And", App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 10 (* L *))), App (App (App (Const "Between", Bvar 9 (* b *)), Bvar 8 (* c *)), Bvar 0 (* a *)))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 7 (* p_list *)), Bvar 6 (* l_list *)), Bvar 5 (* c_list *)))
                        ))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_sameside_of_not_online :
    (L : Line) -> (b : Point) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    (OnLine b L -> False) ->
    Exists Point (fun (a : Point) => And (SameSide a b L) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_sameside_of_not_online";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* b : *)Const "Point",
        Forall ((* p_list : *)App (Const "List", Const "Point"),
          Forall ((* l_list : *)App (Const "List", Const "Line"),
            Forall ((* c_list : *)App (Const "List", Const "Circle"),
              Forall (Forall (App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 4 (* L *)),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                  App (App (Const "And", App (App (App (Const "SameSide", Bvar 0 (* a *)), Bvar 5 (* b *)), Bvar 6 (* L *))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 4 (* p_list *)), Bvar 3 (* l_list *)), Bvar 2 (* c_list *)))
                ))
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_oppositeside_of_not_online :
    (L : Line) -> (b : Point) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    (OnLine b L -> False) ->
    Exists Point (fun (a : Point) =>
      And (And (OnLine a L -> False)
          (SameSide a b L -> False)) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_oppositeside_of_not_online";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* b : *)Const "Point",
        Forall ((* p_list : *)App (Const "List", Const "Point"),
          Forall ((* l_list : *)App (Const "List", Const "Line"),
            Forall ((* c_list : *)App (Const "List", Const "Circle"),
              Forall (Forall (App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 4 (* L *)),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                  App (App (Const "And", App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 6 (* L *)),
                    Const "False"
                  )), Forall (App (App (App (Const "SameSide", Bvar 0 (* a *)), Bvar 5 (* b *)), Bvar 6 (* L *)),
                    Const "False"
                  ))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 4 (* p_list *)), Bvar 3 (* l_list *)), Bvar 2 (* c_list *)))
                ))
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_on_circle :
    (aa : Circle) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) -> (Not (List.mem Circle aa c_list)) ->
    Exists Point (fun (a : Point) => And (OnCircle a aa) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_on_circle";
  [%expect
    {|
    Forall ((* aa : *)Const "Circle",
      Forall ((* p_list : *)App (Const "List", Const "Point"),
        Forall ((* l_list : *)App (Const "List", Const "Line"),
          Forall ((* c_list : *)App (Const "List", Const "Circle"),
            Forall (App (Const "Not", App (App (App (Const "List.mem", Const "Circle"), Bvar 3 (* aa *)), Bvar 0 (* c_list *))),
              App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 5 (* aa *))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 4 (* p_list *)), Bvar 3 (* l_list *)), Bvar 2 (* c_list *)))
              ))
            )
          )
        )
      )
    )
    |}];

  (* pt_inside_circle :
    (aa : Circle) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    Exists Point (fun (a : Point) => And (InCircle a aa) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_inside_circle";
  [%expect
    {|
    Forall ((* aa : *)Const "Circle",
      Forall ((* p_list : *)App (Const "List", Const "Point"),
        Forall ((* l_list : *)App (Const "List", Const "Line"),
          Forall ((* c_list : *)App (Const "List", Const "Circle"),
            App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
              App (App (Const "And", App (App (Const "InCircle", Bvar 0 (* a *)), Bvar 4 (* aa *))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 3 (* p_list *)), Bvar 2 (* l_list *)), Bvar 1 (* c_list *)))
            ))
          )
        )
      )
    )
    |}];

  (* pt_outside_circle :
    (aa : Circle) -> (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    Exists Point (fun (a : Point) =>
      And (And (OnCircle a aa -> False)
          (InCircle a aa -> False)) (distinct_from a p_list l_list c_list)) *)
  show_kterm "pt_outside_circle";
  [%expect
    {|
    Forall ((* aa : *)Const "Circle",
      Forall ((* p_list : *)App (Const "List", Const "Point"),
        Forall ((* l_list : *)App (Const "List", Const "Line"),
          Forall ((* c_list : *)App (Const "List", Const "Circle"),
            App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
              App (App (Const "And", App (App (Const "And", Forall (App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 4 (* aa *)),
                Const "False"
              )), Forall (App (App (Const "InCircle", Bvar 0 (* a *)), Bvar 4 (* aa *)),
                Const "False"
              ))), App (App (App (App (Const "distinct_from", Bvar 0 (* a *)), Bvar 3 (* p_list *)), Bvar 2 (* l_list *)), Bvar 1 (* c_list *)))
            ))
          )
        )
      )
    )
    |}];

  (* line_of_pts :
    (a : Point) -> (b : Point) -> (Eq Point a b -> False) ->
    Exists Line (fun (L : Line) =>
      And (OnLine a L) (OnLine b L)) *)
  show_kterm "line_of_pts";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 (* a *)), Bvar 0 (* b *)),
          Const "False"
        ),
          App (App (Const "Exists", Const "Line"), Lam ((* L : *)Const "Line",
            App (App (Const "And", App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 0 (* L *))), App (App (Const "OnLine", Bvar 2 (* b *)), Bvar 0 (* L *)))
          ))
        )
      )
    )
    |}];

  (* circle_of_ne :
    (a : Point) -> (b : Point) -> (Eq Point a b -> False) ->
    Exists Circle (fun (aa : Circle) =>
      And (CenterCircle a aa) (OnCircle b aa)) *)
  show_kterm "circle_of_ne";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 (* a *)), Bvar 0 (* b *)),
          Const "False"
        ),
          App (App (Const "Exists", Const "Circle"), Lam ((* aa : *)Const "Circle",
            App (App (Const "And", App (App (Const "CenterCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))), App (App (Const "OnCircle", Bvar 2 (* b *)), Bvar 0 (* aa *)))
          ))
        )
      )
    )
    |}];

  (* pt_of_linesinter :
    (L : Line) -> (M : Line) -> LinesInter L M ->
    Exists Point (fun (a : Point) =>
      And (OnLine a L) (OnLine a M)) *)
  show_kterm "pt_of_linesinter";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* M : *)Const "Line",
        Forall (App (App (Const "LinesInter", Bvar 1 (* L *)), Bvar 0 (* M *)),
          App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
            App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 3 (* L *))), App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 2 (* M *)))
          ))
        )
      )
    )
    |}];

  (* pt_of_linecircleinter :
    (L : Line) -> (aa : Circle) -> LineCircleInter L aa ->
    Exists Point (fun (a : Point) =>
      And (OnLine a L) (OnCircle a aa)) *)
  show_kterm "pt_of_linecircleinter";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* aa : *)Const "Circle",
        Forall (App (App (Const "LineCircleInter", Bvar 1 (* L *)), Bvar 0 (* aa *)),
          App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
            App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 3 (* L *))), App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 2 (* aa *)))
          ))
        )
      )
    )
    |}];

  (* pts_of_linecircleinter :
    (L : Line) -> (aa : Circle) -> LineCircleInter L aa ->
    Exists Point (fun (a : Point) =>
      Exists Point (fun (b : Point) =>
        And (Eq Point a b -> False)
        (And (OnLine a L)
        (And (OnLine b L)
        (And (OnCircle a aa) (OnCircle b aa)))))) *)
  show_kterm "pts_of_linecircleinter";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* aa : *)Const "Circle",
        Forall (App (App (Const "LineCircleInter", Bvar 1 (* L *)), Bvar 0 (* aa *)),
          App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
            App (App (Const "Exists", Const "Point"), Lam ((* b : *)Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 (* a *)), Bvar 0 (* b *)),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnLine", Bvar 1 (* a *)), Bvar 4 (* L *))), App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* b *)), Bvar 4 (* L *))), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 (* a *)), Bvar 3 (* aa *))), App (App (Const "OnCircle", Bvar 0 (* b *)), Bvar 3 (* aa *))))))
            ))
          ))
        )
      )
    )
    |}];

  (* pt_oncircle_between_inside_outside :
    (L : Line) -> (aa : Circle) -> (b : Point) -> (c : Point) ->
    OnLine b L -> OnLine c L ->
    InCircle b aa ->
    (OnCircle c aa -> False) -> (InCircle c aa -> False) ->
    Exists Point (fun (a : Point) =>
      And (OnLine a L)
      (And (OnCircle a aa) (Between b a c))) *)
  show_kterm "pt_oncircle_between_inside_outside";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* aa : *)Const "Circle",
        Forall ((* b : *)Const "Point",
          Forall ((* c : *)Const "Point",
            Forall (App (App (Const "OnLine", Bvar 1 (* b *)), Bvar 3 (* L *)),
              Forall (App (App (Const "OnLine", Bvar 1 (* c *)), Bvar 4 (* L *)),
                Forall (App (App (Const "InCircle", Bvar 3 (* b *)), Bvar 4 (* aa *)),
                  Forall (Forall (App (App (Const "OnCircle", Bvar 3 (* c *)), Bvar 5 (* aa *)),
                    Const "False"
                  ),
                    Forall (Forall (App (App (Const "InCircle", Bvar 4 (* c *)), Bvar 6 (* aa *)),
                      Const "False"
                    ),
                      App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                        App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 9 (* L *))), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 8 (* aa *))), App (App (App (Const "Between", Bvar 7 (* b *)), Bvar 0 (* a *)), Bvar 6 (* c *))))
                      ))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_oncircle_extension_from_inside :
    (L : Line) -> (aa : Circle) -> (b : Point) -> (c : Point) ->
    OnLine b L -> OnLine c L ->
    InCircle b aa ->
    (Eq Point c b -> False) ->
    Exists Point (fun (a : Point) =>
      And (OnLine a L)
      (And (OnCircle a aa) (Between a b c))) *)
  show_kterm "pt_oncircle_extension_from_inside";
  [%expect
    {|
    Forall ((* L : *)Const "Line",
      Forall ((* aa : *)Const "Circle",
        Forall ((* b : *)Const "Point",
          Forall ((* c : *)Const "Point",
            Forall (App (App (Const "OnLine", Bvar 1 (* b *)), Bvar 3 (* L *)),
              Forall (App (App (Const "OnLine", Bvar 1 (* c *)), Bvar 4 (* L *)),
                Forall (App (App (Const "InCircle", Bvar 3 (* b *)), Bvar 4 (* aa *)),
                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3 (* c *)), Bvar 4 (* b *)),
                    Const "False"
                  ),
                    App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                      App (App (Const "And", App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 8 (* L *))), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 7 (* aa *))), App (App (App (Const "Between", Bvar 0 (* a *)), Bvar 6 (* b *)), Bvar 5 (* c *))))
                    ))
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_of_circlesinter :
    (aa : Circle) -> (bb : Circle) -> CirclesInter aa bb ->
    Exists Point (fun (a : Point) =>
      And (OnCircle a aa) (OnCircle a bb)) *)
  show_kterm "pt_of_circlesinter";
  [%expect
    {|
    Forall ((* aa : *)Const "Circle",
      Forall ((* bb : *)Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1 (* aa *)), Bvar 0 (* bb *)),
          App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
            App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 3 (* aa *))), App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 2 (* bb *)))
          ))
        )
      )
    )
    |}];

  (* pts_of_circlesinter :
    (aa : Circle) -> (bb : Circle) -> CirclesInter aa bb ->
    Exists Point (fun (a : Point) =>
      Exists Point (fun (b : Point) =>
        And (Eq Point a b -> False)
        (And (OnCircle a aa)
        (And (OnCircle a bb)
        (And (OnCircle b aa) (OnCircle b bb)))))) *)
  show_kterm "pts_of_circlesinter";
  [%expect
    {|
    Forall ((* aa : *)Const "Circle",
      Forall ((* bb : *)Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1 (* aa *)), Bvar 0 (* bb *)),
          App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
            App (App (Const "Exists", Const "Point"), Lam ((* b : *)Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 (* a *)), Bvar 0 (* b *)),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 (* a *)), Bvar 4 (* aa *))), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 (* a *)), Bvar 3 (* bb *))), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* b *)), Bvar 4 (* aa *))), App (App (Const "OnCircle", Bvar 0 (* b *)), Bvar 3 (* bb *))))))
            ))
          ))
        )
      )
    )
    |}];

  (* pt_sameside_of_circlesinter :
    (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) -> (aa : Circle) -> (bb : Circle) ->
    OnLine c L -> OnLine d L -> (OnLine b L -> False) ->
    CenterCircle c aa -> CenterCircle d bb -> CirclesInter aa bb ->
    Exists Point (fun (a : Point) =>
      And (SameSide a b L)
      (And (OnCircle a aa) (OnCircle a bb))) *)
  show_kterm "pt_sameside_of_circlesinter";
  [%expect
    {|
    Forall ((* b : *)Const "Point",
      Forall ((* c : *)Const "Point",
        Forall ((* d : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall ((* aa : *)Const "Circle",
              Forall ((* bb : *)Const "Circle",
                Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 2 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* d *)), Bvar 3 (* L *)),
                    Forall (Forall (App (App (Const "OnLine", Bvar 7 (* b *)), Bvar 4 (* L *)),
                      Const "False"
                    ),
                      Forall (App (App (Const "CenterCircle", Bvar 7 (* c *)), Bvar 4 (* aa *)),
                        Forall (App (App (Const "CenterCircle", Bvar 7 (* d *)), Bvar 4 (* bb *)),
                          Forall (App (App (Const "CirclesInter", Bvar 6 (* aa *)), Bvar 5 (* bb *)),
                            App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                              App (App (Const "And", App (App (App (Const "SameSide", Bvar 0 (* a *)), Bvar 12 (* b *)), Bvar 9 (* L *))), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 8 (* aa *))), App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 7 (* bb *))))
                            ))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_oppositeside_of_circlesinter :
    (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) -> (aa : Circle) -> (bb : Circle) ->
    OnLine c L -> OnLine d L -> (OnLine b L -> False) ->
    CenterCircle c aa -> CenterCircle d bb -> CirclesInter aa bb ->
    Exists Point (fun (a : Point) =>
      And (OnLine a L -> False)
      (And (SameSide a b L -> False)
          (And (OnCircle a aa) (OnCircle a bb)))) *)
  show_kterm "pt_oppositeside_of_circlesinter";
  [%expect
    {|
    Forall ((* b : *)Const "Point",
      Forall ((* c : *)Const "Point",
        Forall ((* d : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall ((* aa : *)Const "Circle",
              Forall ((* bb : *)Const "Circle",
                Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 2 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* d *)), Bvar 3 (* L *)),
                    Forall (Forall (App (App (Const "OnLine", Bvar 7 (* b *)), Bvar 4 (* L *)),
                      Const "False"
                    ),
                      Forall (App (App (Const "CenterCircle", Bvar 7 (* c *)), Bvar 4 (* aa *)),
                        Forall (App (App (Const "CenterCircle", Bvar 7 (* d *)), Bvar 4 (* bb *)),
                          Forall (App (App (Const "CirclesInter", Bvar 6 (* aa *)), Bvar 5 (* bb *)),
                            App (App (Const "Exists", Const "Point"), Lam ((* a : *)Const "Point",
                              App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0 (* a *)), Bvar 9 (* L *)),
                                Const "False"
                              )), App (App (Const "And", Forall (App (App (App (Const "SameSide", Bvar 0 (* a *)), Bvar 12 (* b *)), Bvar 9 (* L *)),
                                Const "False"
                              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 8 (* aa *))), App (App (Const "OnCircle", Bvar 0 (* a *)), Bvar 7 (* bb *)))))
                            ))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* two_distinct_points_determine_unique_line :
    (a: Point) -> (b : Point) -> (L : Line) -> (M : Line) -> 
    (Eq Point a b -> False) ->
    OnLine a L -> OnLine b L -> OnLine a M -> OnLine b M ->
    Eq Line L M *)
  show_kterm "two_distinct_points_determine_unique_line";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* L : *)Const "Line",
          Forall ((* M : *)Const "Line",
            Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3 (* a *)), Bvar 2 (* b *)),
              Const "False"
            ),
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 2 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 3 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 6 (* a *)), Bvar 3 (* M *)),
                    Forall (App (App (Const "OnLine", Bvar 6 (* b *)), Bvar 4 (* M *)),
                      App (App (App (Const "Eq", Const "Line"), Bvar 6 (* L *)), Bvar 5 (* M *))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* circle_has_unique_center : 
    (a : Point) -> (b : Point) -> (aa : Circle) ->
    CenterCircle a aa -> CenterCircle b aa ->
    Eq Point a b *)
  show_kterm "circle_has_unique_center";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* aa : *)Const "Circle",
          Forall (App (App (Const "CenterCircle", Bvar 2 (* a *)), Bvar 0 (* aa *)),
            Forall (App (App (Const "CenterCircle", Bvar 2 (* b *)), Bvar 1 (* aa *)),
              App (App (App (Const "Eq", Const "Point"), Bvar 4 (* a *)), Bvar 3 (* b *))
            )
          )
        )
      )
    )
    |}];

  (* center_lies_inside_circle : 
    (a : Point) -> (aa : Circle) ->
    CenterCircle a aa -> InCircle a aa *)
  show_kterm "center_lies_inside_circle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* aa : *)Const "Circle",
        Forall (App (App (Const "CenterCircle", Bvar 1 (* a *)), Bvar 0 (* aa *)),
          App (App (Const "InCircle", Bvar 2 (* a *)), Bvar 1 (* aa *))
        )
      )
    )
    |}];

  (* inside_implies_not_on_circle :
    (a: Point) -> (aa: Circle) ->
    InCircle a aa -> (OnCircle a aa -> False) *)
  show_kterm "inside_implies_not_on_circle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* aa : *)Const "Circle",
        Forall (App (App (Const "InCircle", Bvar 1 (* a *)), Bvar 0 (* aa *)),
          Forall (App (App (Const "OnCircle", Bvar 2 (* a *)), Bvar 1 (* aa *)),
            Const "False"
          )
        )
      )
    )
    |}];

  (* between_distinct: (a: Point) -> (b: Point) -> (c : Point) -> 
  (Between a b c) -> 
  (And (Between c b a)
  (And (Not (Eq Point a b)) 
  (And (Not (Eq Point a c))
      (Not (Between b a c))
  ))) *)
  show_kterm "between_distinct";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall (App (App (App (Const "Between", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* c *)),
            App (App (Const "And", App (App (App (Const "Between", Bvar 1 (* c *)), Bvar 2 (* b *)), Bvar 3 (* a *))), App (App (Const "And", App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 3 (* a *)), Bvar 2 (* b *)))), App (App (Const "And", App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 3 (* a *)), Bvar 1 (* c *)))), App (Const "Not", App (App (App (Const "Between", Bvar 2 (* b *)), Bvar 3 (* a *)), Bvar 1 (* c *))))))
          )
        )
      )
    )
    |}];

  (* between_collinear_right: (a: Point) -> (b: Point) -> (c : Point) -> (L : Line) -> 
  (Between a b c) -> (OnLine a L) -> (OnLine b L) ->
  (OnLine c L) *)
  show_kterm "between_collinear_right";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 1 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 2 (* L *)),
                  App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 3 (* L *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* between_collinear_middle: (a: Point) -> (b: Point) -> (c : Point) -> (L : Line) -> 
  (Between a b c) -> (OnLine a L) -> (OnLine c L) ->
  (OnLine b L) *)
  show_kterm "between_collinear_middle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 1 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 3 (* c *)), Bvar 2 (* L *)),
                  App (App (Const "OnLine", Bvar 5 (* b *)), Bvar 3 (* L *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* between_in: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) ->
  (Between a b c) -> (Between a d b) ->
  (Between a d c) *)
  show_kterm "between_in";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (App (Const "Between", Bvar 4 (* a *)), Bvar 1 (* d *)), Bvar 3 (* b *)),
                App (App (App (Const "Between", Bvar 5 (* a *)), Bvar 2 (* d *)), Bvar 3 (* c *))
              )
            )
          )
        )
      )
    )
    |}];

  (* between_out: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) ->
    (Between a b c) -> (Between b c d) ->
    (Between a b d) *)
  show_kterm "between_out";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (App (Const "Between", Bvar 3 (* b *)), Bvar 2 (* c *)), Bvar 1 (* d *)),
                App (App (App (Const "Between", Bvar 5 (* a *)), Bvar 4 (* b *)), Bvar 2 (* d *))
              )
            )
          )
        )
      )
    )
    |}];

  (* between_linear: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
  (OnLine a L) -> (OnLine b L) -> (OnLine c L) ->
  (Not (Eq Point a b)) -> (Not (Eq Point b c)) -> (Not (Eq Point a c)) ->
    (Or (Between a b c) (Or (Between b a c) (Between a c b))) *)
  show_kterm "between_linear";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 0 (* L *)),
              Forall (App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 1 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 3 (* c *)), Bvar 2 (* L *)),
                  Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 6 (* a *)), Bvar 5 (* b *))),
                    Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 6 (* b *)), Bvar 5 (* c *))),
                      Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 8 (* a *)), Bvar 6 (* c *))),
                        App (App (Const "Or", App (App (App (Const "Between", Bvar 9 (* a *)), Bvar 8 (* b *)), Bvar 7 (* c *))), App (App (Const "Or", App (App (App (Const "Between", Bvar 8 (* b *)), Bvar 9 (* a *)), Bvar 7 (* c *))), App (App (App (Const "Between", Bvar 9 (* a *)), Bvar 7 (* c *)), Bvar 8 (* b *))))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* between_separation: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) ->
    (Between a b c) -> (Between a b d) ->
    (Not (Between c b d)) *)
  show_kterm "between_separation";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (App (Const "Between", Bvar 4 (* a *)), Bvar 3 (* b *)), Bvar 1 (* d *)),
                App (Const "Not", App (App (App (Const "Between", Bvar 3 (* c *)), Bvar 4 (* b *)), Bvar 2 (* d *)))
              )
            )
          )
        )
      )
    )
    |}];

  (* same_side_refl: (a : Point) -> (L : Line) ->
    (Not (OnLine a L)) ->
    (SameSide a a L) *)
  show_kterm "same_side_refl";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* L : *)Const "Line",
        Forall (App (Const "Not", App (App (Const "OnLine", Bvar 1 (* a *)), Bvar 0 (* L *))),
          App (App (App (Const "SameSide", Bvar 2 (* a *)), Bvar 2 (* a *)), Bvar 1 (* L *))
        )
      )
    )
    |}];

  (* same_side_symm: (a : Point) -> (b : Point) -> (L : Line) ->
    (SameSide a b L) ->
    (SameSide b a L) *)
  show_kterm "same_side_symm";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* L : *)Const "Line",
          Forall (App (App (App (Const "SameSide", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* L *)),
            App (App (App (Const "SameSide", Bvar 2 (* b *)), Bvar 3 (* a *)), Bvar 1 (* L *))
          )
        )
      )
    )
    |}];

  (* same_side_not_on_line: (a : Point) -> (b : Point) -> (L : Line) ->
    (SameSide a b L) ->
    (Not (OnLine a L)) *)
  show_kterm "same_side_not_on_line";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* L : *)Const "Line",
          Forall (App (App (App (Const "SameSide", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* L *)),
            App (Const "Not", App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 1 (* L *)))
          )
        )
      )
    )
    |}];

  (* same_side_trans: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    (SameSide a b L) ->
    (SameSide a c L) ->
    (SameSide b c L) *)
  show_kterm "same_side_trans";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (App (Const "SameSide", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 0 (* L *)),
              Forall (App (App (App (Const "SameSide", Bvar 4 (* a *)), Bvar 2 (* c *)), Bvar 1 (* L *)),
                App (App (App (Const "SameSide", Bvar 4 (* b *)), Bvar 3 (* c *)), Bvar 2 (* L *))
              )
            )
          )
        )
      )
    )
    |}];

  (* same_side_or: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    (Not (OnLine a L)) ->
    (Not (OnLine b L)) ->
    (Not (OnLine c L)) ->
    (Not (SameSide a b L)) ->
    (Or (SameSide a c L) (SameSide b c L)) *)
  show_kterm "same_side_or";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (Const "Not", App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 0 (* L *))),
              Forall (App (Const "Not", App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 1 (* L *))),
                Forall (App (Const "Not", App (App (Const "OnLine", Bvar 3 (* c *)), Bvar 2 (* L *))),
                  Forall (App (Const "Not", App (App (App (Const "SameSide", Bvar 6 (* a *)), Bvar 5 (* b *)), Bvar 3 (* L *))),
                    App (App (Const "Or", App (App (App (Const "SameSide", Bvar 7 (* a *)), Bvar 5 (* c *)), Bvar 4 (* L *))), App (App (App (Const "SameSide", Bvar 6 (* b *)), Bvar 5 (* c *)), Bvar 4 (* L *)))
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pasch_sameside :
    (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    Between a b c -> SameSide a c L ->
    SameSide a b L *)
  show_kterm "pasch_sameside";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (App (Const "SameSide", Bvar 4 (* a *)), Bvar 2 (* c *)), Bvar 1 (* L *)),
                App (App (App (Const "SameSide", Bvar 5 (* a *)), Bvar 4 (* b *)), Bvar 2 (* L *))
              )
            )
          )
        )
      )
    )
    |}];

  (* pasch_online_sameside :
    (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    Between a b c -> OnLine a L -> (OnLine b L -> False) ->
    SameSide b c L *)
  show_kterm "pasch_online_sameside";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 1 (* L *)),
                Forall (Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 2 (* L *)),
                  Const "False"
                ),
                  App (App (App (Const "SameSide", Bvar 5 (* b *)), Bvar 4 (* c *)), Bvar 3 (* L *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pasch_online_not_sameside :
    (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    Between a b c -> OnLine b L ->
    (SameSide a c L -> False) *)
  show_kterm "pasch_online_not_sameside";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *)),
              Forall (App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 1 (* L *)),
                Forall (App (App (App (Const "SameSide", Bvar 5 (* a *)), Bvar 3 (* c *)), Bvar 2 (* L *)),
                  Const "False"
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* pasch_intersection_between :
    (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) -> (M : Line) ->
    (Eq Line L M -> False) ->
    OnLine b L -> OnLine b M ->
    OnLine a M -> OnLine c M ->
    (Eq Point a b -> False) -> (Eq Point c b -> False) ->
    (SameSide a c L -> False) ->
    Between a b c *)
  show_kterm "pasch_intersection_between";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall ((* M : *)Const "Line",
              Forall (Forall (App (App (App (Const "Eq", Const "Line"), Bvar 1 (* L *)), Bvar 0 (* M *)),
                Const "False"
              ),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 2 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 5 (* b *)), Bvar 2 (* M *)),
                    Forall (App (App (Const "OnLine", Bvar 7 (* a *)), Bvar 3 (* M *)),
                      Forall (App (App (Const "OnLine", Bvar 6 (* c *)), Bvar 4 (* M *)),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9 (* a *)), Bvar 8 (* b *)),
                          Const "False"
                        ),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 8 (* c *)), Bvar 9 (* b *)),
                            Const "False"
                          ),
                            Forall (Forall (App (App (App (Const "SameSide", Bvar 11 (* a *)), Bvar 9 (* c *)), Bvar 8 (* L *)),
                              Const "False"
                            ),
                              App (App (App (Const "Between", Bvar 12 (* a *)), Bvar 11 (* b *)), Bvar 10 (* c *))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* triple_incidence_1: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) ->
    (L : Line) -> (M : Line) -> (N : Line) ->
    (OnLine a L) -> (OnLine a M) -> (OnLine a N) ->
    (OnLine b L) -> (OnLine c M) -> (OnLine d N) ->
    (SameSide c d L) ->
    (SameSide b c N) ->
    (Not (SameSide b d M)) *)
  show_kterm "triple_incidence_1";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall ((* M : *)Const "Line",
                Forall ((* N : *)Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 6 (* a *)), Bvar 2 (* L *)),
                    Forall (App (App (Const "OnLine", Bvar 7 (* a *)), Bvar 2 (* M *)),
                      Forall (App (App (Const "OnLine", Bvar 8 (* a *)), Bvar 2 (* N *)),
                        Forall (App (App (Const "OnLine", Bvar 8 (* b *)), Bvar 5 (* L *)),
                          Forall (App (App (Const "OnLine", Bvar 8 (* c *)), Bvar 5 (* M *)),
                            Forall (App (App (Const "OnLine", Bvar 8 (* d *)), Bvar 5 (* N *)),
                              Forall (App (App (App (Const "SameSide", Bvar 10 (* c *)), Bvar 9 (* d *)), Bvar 8 (* L *)),
                                Forall (App (App (App (Const "SameSide", Bvar 12 (* b *)), Bvar 11 (* c *)), Bvar 7 (* N *)),
                                  App (Const "Not", App (App (App (Const "SameSide", Bvar 13 (* b *)), Bvar 11 (* d *)), Bvar 9 (* M *)))
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* triple_incidence_2: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) ->
    (L : Line) -> (M : Line) -> (N : Line) ->
    (OnLine a L) -> (OnLine a M) -> (OnLine a N) ->
    (OnLine b L) -> (OnLine c M) -> (OnLine d N) ->
    (SameSide c d L) ->
    (Not (SameSide b d M)) ->
    (Not (OnLine d M)) ->
    (Not (Eq Point b a)) ->
    (SameSide b c N) *)
  show_kterm "triple_incidence_2";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall ((* M : *)Const "Line",
                Forall ((* N : *)Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 6 (* a *)), Bvar 2 (* L *)),
                    Forall (App (App (Const "OnLine", Bvar 7 (* a *)), Bvar 2 (* M *)),
                      Forall (App (App (Const "OnLine", Bvar 8 (* a *)), Bvar 2 (* N *)),
                        Forall (App (App (Const "OnLine", Bvar 8 (* b *)), Bvar 5 (* L *)),
                          Forall (App (App (Const "OnLine", Bvar 8 (* c *)), Bvar 5 (* M *)),
                            Forall (App (App (Const "OnLine", Bvar 8 (* d *)), Bvar 5 (* N *)),
                              Forall (App (App (App (Const "SameSide", Bvar 10 (* c *)), Bvar 9 (* d *)), Bvar 8 (* L *)),
                                Forall (App (Const "Not", App (App (App (Const "SameSide", Bvar 12 (* b *)), Bvar 10 (* d *)), Bvar 8 (* M *))),
                                  Forall (App (Const "Not", App (App (Const "OnLine", Bvar 11 (* d *)), Bvar 9 (* M *))),
                                    Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 14 (* b *)), Bvar 15 (* a *))),
                                      App (App (App (Const "SameSide", Bvar 15 (* b *)), Bvar 14 (* c *)), Bvar 10 (* N *))
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* triple_incidence_3: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (e : Point) ->
    (L : Line) -> (M : Line) -> (N : Line) ->
    (OnLine a L) -> (OnLine a M) -> (OnLine a N) ->
    (OnLine b L) -> (OnLine c M) -> (OnLine d N) ->
    (SameSide c d L) ->
    (SameSide b c N) ->
    (SameSide d e M) ->
    (SameSide c e N) ->
    (SameSide c e L) *)
  show_kterm "triple_incidence_3";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* e : *)Const "Point",
              Forall ((* L : *)Const "Line",
                Forall ((* M : *)Const "Line",
                  Forall ((* N : *)Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 7 (* a *)), Bvar 2 (* L *)),
                      Forall (App (App (Const "OnLine", Bvar 8 (* a *)), Bvar 2 (* M *)),
                        Forall (App (App (Const "OnLine", Bvar 9 (* a *)), Bvar 2 (* N *)),
                          Forall (App (App (Const "OnLine", Bvar 9 (* b *)), Bvar 5 (* L *)),
                            Forall (App (App (Const "OnLine", Bvar 9 (* c *)), Bvar 5 (* M *)),
                              Forall (App (App (Const "OnLine", Bvar 9 (* d *)), Bvar 5 (* N *)),
                                Forall (App (App (App (Const "SameSide", Bvar 11 (* c *)), Bvar 10 (* d *)), Bvar 8 (* L *)),
                                  Forall (App (App (App (Const "SameSide", Bvar 13 (* b *)), Bvar 12 (* c *)), Bvar 7 (* N *)),
                                    Forall (App (App (App (Const "SameSide", Bvar 12 (* d *)), Bvar 11 (* e *)), Bvar 9 (* M *)),
                                      Forall (App (App (App (Const "SameSide", Bvar 14 (* c *)), Bvar 12 (* e *)), Bvar 9 (* N *)),
                                        App (App (App (Const "SameSide", Bvar 15 (* c *)), Bvar 13 (* e *)), Bvar 12 (* L *))
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* circle_chord_between: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) -> (aa : Circle) ->
    (OnLine a L) -> (OnLine b L) -> (OnLine c L) ->
    (InCircle a aa) -> 
    (OnCircle b aa) -> (OnCircle c aa) ->
    (Not (Eq Point b c)) ->
    (Between b a c) *)
  show_kterm "circle_chord_between";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall ((* aa : *)Const "Circle",
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 1 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 2 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 3 (* L *)),
                    Forall (App (App (Const "InCircle", Bvar 7 (* a *)), Bvar 3 (* aa *)),
                      Forall (App (App (Const "OnCircle", Bvar 7 (* b *)), Bvar 4 (* aa *)),
                        Forall (App (App (Const "OnCircle", Bvar 7 (* c *)), Bvar 5 (* aa *)),
                          Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 9 (* b *)), Bvar 8 (* c *))),
                            App (App (App (Const "Between", Bvar 10 (* b *)), Bvar 11 (* a *)), Bvar 9 (* c *))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* circle_convex: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) ->
    (Or (InCircle a aa) (OnCircle a aa)) ->
    (Or (InCircle b aa) (OnCircle b aa)) ->
    (Between a c b) ->
    (InCircle c aa) *)
  show_kterm "circle_convex";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))), App (App (Const "OnCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))),
              Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3 (* b *)), Bvar 1 (* aa *))), App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 1 (* aa *))),
                Forall (App (App (App (Const "Between", Bvar 5 (* a *)), Bvar 3 (* c *)), Bvar 4 (* b *)),
                  App (App (Const "InCircle", Bvar 4 (* c *)), Bvar 3 (* aa *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* circle_extend_ray_outside: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) ->
    (Or (InCircle a aa) (OnCircle a aa)) ->
    (Not (InCircle c aa)) ->
    (Between a c b) ->
    (And (Not (InCircle b aa)) (Not (OnCircle b aa))) *)
  show_kterm "circle_extend_ray_outside";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))), App (App (Const "OnCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))),
              Forall (App (Const "Not", App (App (Const "InCircle", Bvar 2 (* c *)), Bvar 1 (* aa *))),
                Forall (App (App (App (Const "Between", Bvar 5 (* a *)), Bvar 3 (* c *)), Bvar 4 (* b *)),
                  App (App (Const "And", App (Const "Not", App (App (Const "InCircle", Bvar 5 (* b *)), Bvar 3 (* aa *)))), App (Const "Not", App (App (Const "OnCircle", Bvar 5 (* b *)), Bvar 3 (* aa *))))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* circle_intersect_opposite_sides: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> 
  (L : Line) ->
  (aa : Circle) -> (bb : Circle) ->
    (Not (Eq Circle aa bb)) ->
    (OnCircle c aa) -> (OnCircle c bb) ->
    (OnCircle d aa) -> (OnCircle d bb) ->
    (Not (Eq Point c d)) ->
    (CenterCircle a aa) -> (CenterCircle b bb) ->
    (OnLine a L) ->
    (OnLine b L) ->
    (Not (SameSide c d L)) *)
  show_kterm "circle_intersect_opposite_sides";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall ((* aa : *)Const "Circle",
                Forall ((* bb : *)Const "Circle",
                  Forall (App (Const "Not", App (App (App (Const "Eq", Const "Circle"), Bvar 1 (* aa *)), Bvar 0 (* bb *))),
                    Forall (App (App (Const "OnCircle", Bvar 5 (* c *)), Bvar 2 (* aa *)),
                      Forall (App (App (Const "OnCircle", Bvar 6 (* c *)), Bvar 2 (* bb *)),
                        Forall (App (App (Const "OnCircle", Bvar 6 (* d *)), Bvar 4 (* aa *)),
                          Forall (App (App (Const "OnCircle", Bvar 7 (* d *)), Bvar 4 (* bb *)),
                            Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 9 (* c *)), Bvar 8 (* d *))),
                              Forall (App (App (Const "CenterCircle", Bvar 12 (* a *)), Bvar 7 (* aa *)),
                                Forall (App (App (Const "CenterCircle", Bvar 12 (* b *)), Bvar 7 (* bb *)),
                                  Forall (App (App (Const "OnLine", Bvar 14 (* a *)), Bvar 10 (* L *)),
                                    Forall (App (App (Const "OnLine", Bvar 14 (* b *)), Bvar 11 (* L *)),
                                      App (Const "Not", App (App (App (Const "SameSide", Bvar 14 (* c *)), Bvar 13 (* d *)), Bvar 12 (* L *)))
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* lines_inter_if_diff_sides: (a : Point) -> (b : Point) -> (L : Line) -> (M : Line) ->
    (Not (SameSide a b L)) ->
    (OnLine a M) ->
    (OnLine b M) ->
    (LinesInter L M) *)
  show_kterm "lines_inter_if_diff_sides";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* L : *)Const "Line",
          Forall ((* M : *)Const "Line",
            Forall (App (Const "Not", App (App (App (Const "SameSide", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* L *))),
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 1 (* M *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 2 (* M *)),
                  App (App (Const "LinesInter", Bvar 4 (* L *)), Bvar 3 (* M *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* line_circle_inter_if_diff_sides: (a : Point) -> (b : Point) -> (L : Line) -> (aa : Circle) ->
    (Or (InCircle a aa) (OnCircle a aa)) ->
    (Or (InCircle b aa) (OnCircle b aa)) ->
    (Not (SameSide a b L)) ->
    (LineCircleInter L aa) *)
  show_kterm "line_circle_inter_if_diff_sides";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* L : *)Const "Line",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))), App (App (Const "OnCircle", Bvar 3 (* a *)), Bvar 0 (* aa *))),
              Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3 (* b *)), Bvar 1 (* aa *))), App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 1 (* aa *))),
                Forall (App (Const "Not", App (App (App (Const "SameSide", Bvar 5 (* a *)), Bvar 4 (* b *)), Bvar 3 (* L *))),
                  App (App (Const "LineCircleInter", Bvar 4 (* L *)), Bvar 3 (* aa *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* line_circle_inter_if_inside_or_on: (a : Point) -> (L : Line) -> (aa : Circle) ->
    (InCircle a aa) ->
    (OnLine a L) ->
    (LineCircleInter L aa) *)
  show_kterm "line_circle_inter_if_inside_or_on";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* L : *)Const "Line",
        Forall ((* aa : *)Const "Circle",
          Forall (App (App (Const "InCircle", Bvar 2 (* a *)), Bvar 0 (* aa *)),
            Forall (App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 2 (* L *)),
              App (App (Const "LineCircleInter", Bvar 3 (* L *)), Bvar 2 (* aa *))
            )
          )
        )
      )
    )
    |}];

  (* circles_inter_if_inside_outside: (a : Point) -> (b : Point) -> (aa : Circle) -> (bb : Circle) ->
    (OnCircle a aa) ->
    (Or (InCircle b aa) (OnCircle b aa)) ->
    (InCircle a bb) ->
    (And (Not (InCircle b bb)) (Not (OnCircle b bb))) ->
    (CirclesInter aa bb) *)
  show_kterm "circles_inter_if_inside_outside";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* aa : *)Const "Circle",
          Forall ((* bb : *)Const "Circle",
            Forall (App (App (Const "OnCircle", Bvar 3 (* a *)), Bvar 1 (* aa *)),
              Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3 (* b *)), Bvar 2 (* aa *))), App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 2 (* aa *))),
                Forall (App (App (Const "InCircle", Bvar 5 (* a *)), Bvar 2 (* bb *)),
                  Forall (App (App (Const "And", App (Const "Not", App (App (Const "InCircle", Bvar 5 (* b *)), Bvar 3 (* bb *)))), App (Const "Not", App (App (Const "OnCircle", Bvar 5 (* b *)), Bvar 3 (* bb *)))),
                    App (App (Const "CirclesInter", Bvar 5 (* aa *)), Bvar 4 (* bb *))
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* circles_inter_if_on_in: (a : Point) -> (b : Point) -> (aa : Circle) -> (bb : Circle) ->
    (OnCircle a aa) -> (InCircle b aa) ->
    (InCircle a bb) -> (OnCircle b bb) ->
    (CirclesInter aa bb) *)
  show_kterm "circles_inter_if_on_in";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* aa : *)Const "Circle",
          Forall ((* bb : *)Const "Circle",
            Forall (App (App (Const "OnCircle", Bvar 3 (* a *)), Bvar 1 (* aa *)),
              Forall (App (App (Const "InCircle", Bvar 3 (* b *)), Bvar 2 (* aa *)),
                Forall (App (App (Const "InCircle", Bvar 5 (* a *)), Bvar 2 (* bb *)),
                  Forall (App (App (Const "OnCircle", Bvar 5 (* b *)), Bvar 3 (* bb *)),
                    App (App (Const "CirclesInter", Bvar 5 (* aa *)), Bvar 4 (* bb *))
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* eq_if_len_zero: (a : Point) -> (b : Point) ->
    (Eq Measure (Length a b) Zero) ->
    (Eq Point a b) *)
  show_kterm "eq_if_len_zero";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 1 (* a *)), Bvar 0 (* b *))), Const "Zero"),
          App (App (App (Const "Eq", Const "Point"), Bvar 2 (* a *)), Bvar 1 (* b *))
        )
      )
    )
    |}];

  (* len_zero_if_eq: (a : Point) -> (b : Point) ->
    (Eq Point a b) ->
    (Eq Measure (Length a b) Zero) *)
  show_kterm "len_zero_if_eq";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 (* a *)), Bvar 0 (* b *)),
          App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 2 (* a *)), Bvar 1 (* b *))), Const "Zero")
        )
      )
    )
    |}];

  (* length_nonneg: (a : Point) -> (b : Point) ->
    (Not (Lt (Length a b) Zero)) *)
  show_kterm "length_nonneg";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        App (Const "Not", App (App (Const "Lt", App (App (Const "Length", Bvar 1 (* a *)), Bvar 0 (* b *))), Const "Zero"))
      )
    )
    |}];

  (* length_symm: (a : Point) -> (b : Point) ->
    (Eq Measure (Length a b) (Length b a)) *)
  show_kterm "length_symm";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 1 (* a *)), Bvar 0 (* b *))), App (App (Const "Length", Bvar 0 (* b *)), Bvar 1 (* a *)))
      )
    )
    |}];

  (* angle_symm: (a : Point) -> (b : Point) -> (c : Point) ->
    (Not (Eq Point a b)) -> (Not (Eq Point b c)) ->
    (Eq Measure (Angle a b c) (Angle c b a)) *)
  show_kterm "angle_symm";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 2 (* a *)), Bvar 1 (* b *))),
            Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 2 (* b *)), Bvar 1 (* c *))),
              App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 4 (* a *)), Bvar 3 (* b *)), Bvar 2 (* c *))), App (App (App (Const "Angle", Bvar 2 (* c *)), Bvar 3 (* b *)), Bvar 4 (* a *)))
            )
          )
        )
      )
    )
    |}];

  (* angle_range: (a : Point) -> (b : Point) -> (c : Point) ->
    (Not (Lt (Angle a b c) Zero)) ->
    (Not (Lt (Add RightAngle RightAngle) (Angle a b c))) *)
  show_kterm "angle_range";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall (App (Const "Not", App (App (Const "Lt", App (App (App (Const "Angle", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* c *))), Const "Zero")),
            App (Const "Not", App (App (Const "Lt", App (App (Const "Add", Const "RightAngle"), Const "RightAngle")), App (App (App (Const "Angle", Bvar 3 (* a *)), Bvar 2 (* b *)), Bvar 1 (* c *))))
          )
        )
      )
    )
    |}];

  (* area_degenerate: (a : Point) -> (b : Point) ->
    (Eq Measure (Area a a b) Zero) *)
  show_kterm "area_degenerate";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 1 (* a *)), Bvar 1 (* a *)), Bvar 0 (* b *))), Const "Zero")
      )
    )
    |}];

  (* area_nonneg: (a : Point) -> (b : Point) -> (c : Point) ->
    (Not (Lt (Area a b c) Zero)) *)
  show_kterm "area_nonneg";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          App (Const "Not", App (App (Const "Lt", App (App (App (Const "Area", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* c *))), Const "Zero"))
        )
      )
    )
    |}];

  (* area_perm: (a : Point) -> (b : Point) -> (c : Point) ->
    (And (Eq Measure (Area a b c) (Area c a b)) (Eq Measure (Area a b c) (Area a c b))) *)
  show_kterm "area_perm";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* c *))), App (App (App (Const "Area", Bvar 0 (* c *)), Bvar 2 (* a *)), Bvar 1 (* b *)))), App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* c *))), App (App (App (Const "Area", Bvar 2 (* a *)), Bvar 0 (* c *)), Bvar 1 (* b *))))
        )
      )
    )
    |}];

  (* area_congruence: (a : Point) -> (b : Point) -> (c : Point) ->
    (a' : Point) -> (b' : Point) -> (c' : Point) ->
    (Eq Measure (Length a b) (Length a' b')) ->
    (Eq Measure (Length b c) (Length b' c')) ->
    (Eq Measure (Angle a b c) (Angle a' b' c')) ->
    (Eq Measure (Angle b c a) (Angle b' c' a')) ->
    (Eq Measure (Angle c a b) (Angle c' a' b')) ->
    (Eq Measure (Area a b c) (Area a' b' c')) *)
  show_kterm "area_congruence";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* a' : *)Const "Point",
            Forall ((* b' : *)Const "Point",
              Forall ((* c' : *)Const "Point",
                Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 5 (* a *)), Bvar 4 (* b *))), App (App (Const "Length", Bvar 2 (* a' *)), Bvar 1 (* b' *))),
                  Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 5 (* b *)), Bvar 4 (* c *))), App (App (Const "Length", Bvar 2 (* b' *)), Bvar 1 (* c' *))),
                    Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 7 (* a *)), Bvar 6 (* b *)), Bvar 5 (* c *))), App (App (App (Const "Angle", Bvar 4 (* a' *)), Bvar 3 (* b' *)), Bvar 2 (* c' *))),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 7 (* b *)), Bvar 6 (* c *)), Bvar 8 (* a *))), App (App (App (Const "Angle", Bvar 4 (* b' *)), Bvar 3 (* c' *)), Bvar 5 (* a' *))),
                        Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 7 (* c *)), Bvar 9 (* a *)), Bvar 8 (* b *))), App (App (App (Const "Angle", Bvar 4 (* c' *)), Bvar 6 (* a' *)), Bvar 5 (* b' *))),
                          App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 10 (* a *)), Bvar 9 (* b *)), Bvar 8 (* c *))), App (App (App (Const "Area", Bvar 7 (* a' *)), Bvar 6 (* b' *)), Bvar 5 (* c' *)))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* between_add_lengths: (a : Point) -> (b : Point) -> (c : Point) ->
    (Between a b c) ->
    (Eq Measure (Add (Length a b) (Length b c)) (Length a c)) *)
  show_kterm "between_add_lengths";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall (App (App (App (Const "Between", Bvar 2 (* a *)), Bvar 1 (* b *)), Bvar 0 (* c *)),
            App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (Const "Length", Bvar 3 (* a *)), Bvar 2 (* b *))), App (App (Const "Length", Bvar 2 (* b *)), Bvar 1 (* c *)))), App (App (Const "Length", Bvar 3 (* a *)), Bvar 1 (* c *)))
          )
        )
      )
    )
    |}];

  (* circle_eq_if_center_and_radius_eq: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) -> (bb : Circle) ->
    (CenterCircle a aa) ->
    (CenterCircle a bb) ->
    (OnCircle b aa) ->
    (OnCircle c bb) ->
    (Eq Measure (Length a b) (Length a c)) ->
    (Eq Circle aa bb) *)
  show_kterm "circle_eq_if_center_and_radius_eq";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall ((* bb : *)Const "Circle",
              Forall (App (App (Const "CenterCircle", Bvar 4 (* a *)), Bvar 1 (* aa *)),
                Forall (App (App (Const "CenterCircle", Bvar 5 (* a *)), Bvar 1 (* bb *)),
                  Forall (App (App (Const "OnCircle", Bvar 5 (* b *)), Bvar 3 (* aa *)),
                    Forall (App (App (Const "OnCircle", Bvar 5 (* c *)), Bvar 3 (* bb *)),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 8 (* a *)), Bvar 7 (* b *))), App (App (Const "Length", Bvar 8 (* a *)), Bvar 6 (* c *))),
                        App (App (App (Const "Eq", Const "Circle"), Bvar 6 (* aa *)), Bvar 5 (* bb *))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* on_circle_if_eq_radius: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) ->
    (CenterCircle a aa) ->
    (OnCircle b aa) ->
    (Eq Measure (Length a c) (Length a b)) ->
    (OnCircle c aa) *)
  show_kterm "on_circle_if_eq_radius";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3 (* a *)), Bvar 0 (* aa *)),
              Forall (App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 1 (* aa *)),
                Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 5 (* a *)), Bvar 3 (* c *))), App (App (Const "Length", Bvar 5 (* a *)), Bvar 4 (* b *))),
                  App (App (Const "OnCircle", Bvar 4 (* c *)), Bvar 3 (* aa *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* eq_radius_if_on_circle: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) ->
    (CenterCircle a aa) ->
    (OnCircle b aa) ->
    (OnCircle c aa) ->
    (Eq Measure (Length a c) (Length a b)) *)
  show_kterm "eq_radius_if_on_circle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3 (* a *)), Bvar 0 (* aa *)),
              Forall (App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 1 (* aa *)),
                Forall (App (App (Const "OnCircle", Bvar 3 (* c *)), Bvar 2 (* aa *)),
                  App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 6 (* a *)), Bvar 4 (* c *))), App (App (Const "Length", Bvar 6 (* a *)), Bvar 5 (* b *)))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* in_circle_if_lt_radius: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) ->
    (CenterCircle a aa) ->
    (OnCircle b aa) ->
    (Lt (Length a c) (Length a b)) ->
    (InCircle c aa) *)
  show_kterm "in_circle_if_lt_radius";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3 (* a *)), Bvar 0 (* aa *)),
              Forall (App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 1 (* aa *)),
                Forall (App (App (Const "Lt", App (App (Const "Length", Bvar 5 (* a *)), Bvar 3 (* c *))), App (App (Const "Length", Bvar 5 (* a *)), Bvar 4 (* b *))),
                  App (App (Const "InCircle", Bvar 4 (* c *)), Bvar 3 (* aa *))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* lt_radius_if_in_circle: (a : Point) -> (b : Point) -> (c : Point) -> (aa : Circle) ->
    (CenterCircle a aa) ->
    (OnCircle b aa) ->
    (InCircle c aa) ->
    (Lt (Length a c) (Length a b)) *)
  show_kterm "lt_radius_if_in_circle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* aa : *)Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3 (* a *)), Bvar 0 (* aa *)),
              Forall (App (App (Const "OnCircle", Bvar 3 (* b *)), Bvar 1 (* aa *)),
                Forall (App (App (Const "InCircle", Bvar 3 (* c *)), Bvar 2 (* aa *)),
                  App (App (Const "Lt", App (App (Const "Length", Bvar 6 (* a *)), Bvar 4 (* c *))), App (App (Const "Length", Bvar 6 (* a *)), Bvar 5 (* b *)))
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* angle_zero_if_on_line: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    (Not (Eq Point a b)) ->
    (Not (Eq Point a c)) ->
    (OnLine a L) ->
    (OnLine b L) ->
    (OnLine c L) -> (Not (Between b a c)) ->
    (Eq Measure (Angle b a c) Zero) *)
  show_kterm "angle_zero_if_on_line";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 3 (* a *)), Bvar 2 (* b *))),
              Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 4 (* a *)), Bvar 2 (* c *))),
                Forall (App (App (Const "OnLine", Bvar 5 (* a *)), Bvar 2 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 5 (* b *)), Bvar 3 (* L *)),
                    Forall (App (App (Const "OnLine", Bvar 5 (* c *)), Bvar 4 (* L *)),
                      Forall (App (Const "Not", App (App (App (Const "Between", Bvar 7 (* b *)), Bvar 8 (* a *)), Bvar 6 (* c *))),
                        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 8 (* b *)), Bvar 9 (* a *)), Bvar 7 (* c *))), Const "Zero")
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* on_line_if_angle_zero: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    (Not (Eq Point a b)) ->
    (Not (Eq Point a c)) ->
    (OnLine a L) ->
    (OnLine b L) ->
    (Eq Measure (Angle b a c) Zero) ->
    (And (OnLine c L) (Not (Between b a c))) *)
  show_kterm "on_line_if_angle_zero";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 3 (* a *)), Bvar 2 (* b *))),
              Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 4 (* a *)), Bvar 2 (* c *))),
                Forall (App (App (Const "OnLine", Bvar 5 (* a *)), Bvar 2 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 5 (* b *)), Bvar 3 (* L *)),
                    Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 6 (* b *)), Bvar 7 (* a *)), Bvar 5 (* c *))), Const "Zero"),
                      App (App (Const "And", App (App (Const "OnLine", Bvar 6 (* c *)), Bvar 5 (* L *))), App (Const "Not", App (App (App (Const "Between", Bvar 7 (* b *)), Bvar 8 (* a *)), Bvar 6 (* c *))))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* angle_add_if_same_side: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) -> (M : Line) ->
    (OnLine a L) -> (OnLine a M) ->
    (OnLine b L) -> (OnLine c M) ->
    (Not (Eq Point a b)) -> 
    (Not (Eq Point a c)) ->
    (Not (OnLine d L)) -> (Not (OnLine d M)) ->
    (Not (Eq Line L M)) ->
    (SameSide b d M) -> (SameSide c d L) ->
    (Eq Measure (Angle b a c) (Add (Angle b a d) (Angle d a c))) *)
  show_kterm "angle_add_if_same_side";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall ((* M : *)Const "Line",
                Forall (App (App (Const "OnLine", Bvar 5 (* a *)), Bvar 1 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 6 (* a *)), Bvar 1 (* M *)),
                    Forall (App (App (Const "OnLine", Bvar 6 (* b *)), Bvar 3 (* L *)),
                      Forall (App (App (Const "OnLine", Bvar 6 (* c *)), Bvar 3 (* M *)),
                        Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 9 (* a *)), Bvar 8 (* b *))),
                          Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 10 (* a *)), Bvar 8 (* c *))),
                            Forall (App (Const "Not", App (App (Const "OnLine", Bvar 8 (* d *)), Bvar 7 (* L *))),
                              Forall (App (Const "Not", App (App (Const "OnLine", Bvar 9 (* d *)), Bvar 7 (* M *))),
                                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Line"), Bvar 9 (* L *)), Bvar 8 (* M *))),
                                  Forall (App (App (App (Const "SameSide", Bvar 13 (* b *)), Bvar 11 (* d *)), Bvar 9 (* M *)),
                                    Forall (App (App (App (Const "SameSide", Bvar 13 (* c *)), Bvar 12 (* d *)), Bvar 11 (* L *)),
                                      App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 15 (* b *)), Bvar 16 (* a *)), Bvar 14 (* c *))), App (App (Const "Add", App (App (App (Const "Angle", Bvar 15 (* b *)), Bvar 16 (* a *)), Bvar 13 (* d *))), App (App (App (Const "Angle", Bvar 13 (* d *)), Bvar 16 (* a *)), Bvar 14 (* c *))))
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* same_side_if_angle_add: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) -> (M : Line) ->
    (OnLine a L) -> (OnLine a M) ->
    (OnLine b L) -> (OnLine c M) ->
    (Not (Eq Point a b)) ->
    (Not (Eq Point a c)) ->
    (Not (OnLine d L)) -> (Not (OnLine d M)) ->
    (Not (Eq Line L M)) ->
    (Eq Measure (Angle b a c) (Add (Angle b a d) (Angle d a c))) ->
    (And (SameSide b d M) (SameSide c d L)) *)
  show_kterm "same_side_if_angle_add";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall ((* M : *)Const "Line",
                Forall (App (App (Const "OnLine", Bvar 5 (* a *)), Bvar 1 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 6 (* a *)), Bvar 1 (* M *)),
                    Forall (App (App (Const "OnLine", Bvar 6 (* b *)), Bvar 3 (* L *)),
                      Forall (App (App (Const "OnLine", Bvar 6 (* c *)), Bvar 3 (* M *)),
                        Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 9 (* a *)), Bvar 8 (* b *))),
                          Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 10 (* a *)), Bvar 8 (* c *))),
                            Forall (App (Const "Not", App (App (Const "OnLine", Bvar 8 (* d *)), Bvar 7 (* L *))),
                              Forall (App (Const "Not", App (App (Const "OnLine", Bvar 9 (* d *)), Bvar 7 (* M *))),
                                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Line"), Bvar 9 (* L *)), Bvar 8 (* M *))),
                                  Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 13 (* b *)), Bvar 14 (* a *)), Bvar 12 (* c *))), App (App (Const "Add", App (App (App (Const "Angle", Bvar 13 (* b *)), Bvar 14 (* a *)), Bvar 11 (* d *))), App (App (App (Const "Angle", Bvar 11 (* d *)), Bvar 14 (* a *)), Bvar 12 (* c *)))),
                                    App (App (Const "And", App (App (App (Const "SameSide", Bvar 14 (* b *)), Bvar 12 (* d *)), Bvar 10 (* M *))), App (App (App (Const "SameSide", Bvar 13 (* c *)), Bvar 12 (* d *)), Bvar 11 (* L *)))
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* right_angle_if_angle_eq: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) ->
    (OnLine a L) -> (OnLine b L) ->
    (Between a c b) ->
    (Not (OnLine d L)) ->
    (Eq Measure (Angle a c d) (Angle d c b)) ->
    (Eq Measure (Angle a c d) RightAngle) *)
  show_kterm "right_angle_if_angle_eq";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 0 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 1 (* L *)),
                  Forall (App (App (App (Const "Between", Bvar 6 (* a *)), Bvar 4 (* c *)), Bvar 5 (* b *)),
                    Forall (App (Const "Not", App (App (Const "OnLine", Bvar 4 (* d *)), Bvar 3 (* L *))),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 8 (* a *)), Bvar 6 (* c *)), Bvar 5 (* d *))), App (App (App (Const "Angle", Bvar 5 (* d *)), Bvar 6 (* c *)), Bvar 7 (* b *))),
                        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 9 (* a *)), Bvar 7 (* c *)), Bvar 6 (* d *))), Const "RightAngle")
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* angle_eq_if_right_angle: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) ->
    (OnLine a L) -> (OnLine b L) ->
    (Between a c b) ->
    (Not (OnLine d L)) ->
    (Eq Measure (Angle a c d) RightAngle) ->
    (Eq Measure (Angle a c d) (Angle d c b)) *)
  show_kterm "angle_eq_if_right_angle";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 0 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 1 (* L *)),
                  Forall (App (App (App (Const "Between", Bvar 6 (* a *)), Bvar 4 (* c *)), Bvar 5 (* b *)),
                    Forall (App (Const "Not", App (App (Const "OnLine", Bvar 4 (* d *)), Bvar 3 (* L *))),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 8 (* a *)), Bvar 6 (* c *)), Bvar 5 (* d *))), Const "RightAngle"),
                        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 9 (* a *)), Bvar 7 (* c *)), Bvar 6 (* d *))), App (App (App (Const "Angle", Bvar 6 (* d *)), Bvar 7 (* c *)), Bvar 8 (* b *)))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* angle_eq_on_same_rays: (a : Point) -> (b : Point) -> (b' : Point) -> (c : Point) -> (c' : Point) -> 
    (L : Line) -> (M : Line) ->
    (OnLine a L) -> (OnLine b L) -> (OnLine b' L) ->
    (OnLine a M) -> (OnLine c M) -> (OnLine c' M) ->
    (Not (Eq Point b a)) -> (Not (Eq Point b' a)) ->
    (Not (Eq Point c a)) -> (Not (Eq Point c' a)) ->
    (Not (Between b a b')) ->
    (Not (Between c a c')) ->
    (Eq Measure (Angle b a c) (Angle b' a c')) *)
  show_kterm "angle_eq_on_same_rays";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* b' : *)Const "Point",
          Forall ((* c : *)Const "Point",
            Forall ((* c' : *)Const "Point",
              Forall ((* L : *)Const "Line",
                Forall ((* M : *)Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 6 (* a *)), Bvar 1 (* L *)),
                    Forall (App (App (Const "OnLine", Bvar 6 (* b *)), Bvar 2 (* L *)),
                      Forall (App (App (Const "OnLine", Bvar 6 (* b' *)), Bvar 3 (* L *)),
                        Forall (App (App (Const "OnLine", Bvar 9 (* a *)), Bvar 3 (* M *)),
                          Forall (App (App (Const "OnLine", Bvar 7 (* c *)), Bvar 4 (* M *)),
                            Forall (App (App (Const "OnLine", Bvar 7 (* c' *)), Bvar 5 (* M *)),
                              Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 11 (* b *)), Bvar 12 (* a *))),
                                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 11 (* b' *)), Bvar 13 (* a *))),
                                  Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 11 (* c *)), Bvar 14 (* a *))),
                                    Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 11 (* c' *)), Bvar 15 (* a *))),
                                      Forall (App (Const "Not", App (App (App (Const "Between", Bvar 15 (* b *)), Bvar 16 (* a *)), Bvar 14 (* b' *))),
                                        Forall (App (Const "Not", App (App (App (Const "Between", Bvar 14 (* c *)), Bvar 17 (* a *)), Bvar 13 (* c' *))),
                                          App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 17 (* b *)), Bvar 18 (* a *)), Bvar 15 (* c *))), App (App (App (Const "Angle", Bvar 16 (* b' *)), Bvar 18 (* a *)), Bvar 14 (* c' *)))
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* lines_inter_if_angle_sum_lt_180: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> 
  (e : Point) -> (L : Line) -> (M : Line) -> (N : Line) ->
    (OnLine a L) -> (OnLine b L) ->
    (OnLine b M) ->(OnLine c M) ->
    (OnLine c N) -> (OnLine d N) ->
    (Not (Eq Point b c)) ->
    (SameSide a d M) ->
    (Lt (Add (Angle a b c) (Angle b c d)) (Add RightAngle RightAngle)) ->
    (LinesInter L N) *)
  show_kterm "lines_inter_if_angle_sum_lt_180";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* e : *)Const "Point",
              Forall ((* L : *)Const "Line",
                Forall ((* M : *)Const "Line",
                  Forall ((* N : *)Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 7 (* a *)), Bvar 2 (* L *)),
                      Forall (App (App (Const "OnLine", Bvar 7 (* b *)), Bvar 3 (* L *)),
                        Forall (App (App (Const "OnLine", Bvar 8 (* b *)), Bvar 3 (* M *)),
                          Forall (App (App (Const "OnLine", Bvar 8 (* c *)), Bvar 4 (* M *)),
                            Forall (App (App (Const "OnLine", Bvar 9 (* c *)), Bvar 4 (* N *)),
                              Forall (App (App (Const "OnLine", Bvar 9 (* d *)), Bvar 5 (* N *)),
                                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 12 (* b *)), Bvar 11 (* c *))),
                                  Forall (App (App (App (Const "SameSide", Bvar 14 (* a *)), Bvar 11 (* d *)), Bvar 8 (* M *)),
                                    Forall (App (App (Const "Lt", App (App (Const "Add", App (App (App (Const "Angle", Bvar 15 (* a *)), Bvar 14 (* b *)), Bvar 13 (* c *))), App (App (App (Const "Angle", Bvar 14 (* b *)), Bvar 13 (* c *)), Bvar 12 (* d *)))), App (App (Const "Add", Const "RightAngle"), Const "RightAngle")),
                                      App (App (Const "LinesInter", Bvar 11 (* L *)), Bvar 9 (* N *))
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* ine_inter_point_on_same_side_if_angle_sum_lt_180: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> 
  (e : Point) -> (L : Line) -> (M : Line) -> (N : Line) ->
    (OnLine a L) -> (OnLine b L) ->
    (OnLine b M) ->(OnLine c M) ->
    (OnLine c N) -> (OnLine d N) ->
    (Not (Eq Point b c)) ->
    (SameSide a d M) ->
    (Lt (Add (Angle a b c) (Angle b c d)) (Add RightAngle RightAngle)) ->   
    (OnLine e L) -> (OnLine e N) ->
    (SameSide e a M) *)
  show_kterm "ine_inter_point_on_same_side_if_angle_sum_lt_180";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* e : *)Const "Point",
              Forall ((* L : *)Const "Line",
                Forall ((* M : *)Const "Line",
                  Forall ((* N : *)Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 7 (* a *)), Bvar 2 (* L *)),
                      Forall (App (App (Const "OnLine", Bvar 7 (* b *)), Bvar 3 (* L *)),
                        Forall (App (App (Const "OnLine", Bvar 8 (* b *)), Bvar 3 (* M *)),
                          Forall (App (App (Const "OnLine", Bvar 8 (* c *)), Bvar 4 (* M *)),
                            Forall (App (App (Const "OnLine", Bvar 9 (* c *)), Bvar 4 (* N *)),
                              Forall (App (App (Const "OnLine", Bvar 9 (* d *)), Bvar 5 (* N *)),
                                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 12 (* b *)), Bvar 11 (* c *))),
                                  Forall (App (App (App (Const "SameSide", Bvar 14 (* a *)), Bvar 11 (* d *)), Bvar 8 (* M *)),
                                    Forall (App (App (Const "Lt", App (App (Const "Add", App (App (App (Const "Angle", Bvar 15 (* a *)), Bvar 14 (* b *)), Bvar 13 (* c *))), App (App (App (Const "Angle", Bvar 14 (* b *)), Bvar 13 (* c *)), Bvar 12 (* d *)))), App (App (Const "Add", Const "RightAngle"), Const "RightAngle")),
                                      Forall (App (App (Const "OnLine", Bvar 12 (* e *)), Bvar 11 (* L *)),
                                        Forall (App (App (Const "OnLine", Bvar 13 (* e *)), Bvar 10 (* N *)),
                                          App (App (App (Const "SameSide", Bvar 14 (* e *)), Bvar 18 (* a *)), Bvar 12 (* M *))
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* on_line_if_area_zero: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    (OnLine a L) -> (OnLine b L) -> (Not (Eq Point a b)) ->
    (Eq Measure (Area a b c) Zero) ->
    (OnLine c L) *)
  show_kterm "on_line_if_area_zero";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 0 (* L *)),
              Forall (App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 1 (* L *)),
                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 5 (* a *)), Bvar 4 (* b *))),
                  Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 6 (* a *)), Bvar 5 (* b *)), Bvar 4 (* c *))), Const "Zero"),
                    App (App (Const "OnLine", Bvar 5 (* c *)), Bvar 4 (* L *))
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* area_zero_if_on_line: (a : Point) -> (b : Point) -> (c : Point) -> (L : Line) ->
    (OnLine a L) -> (OnLine b L) -> (Not (Eq Point a b)) ->
    (OnLine c L) -> 
    (Eq Measure (Area a b c) Zero) *)
  show_kterm "area_zero_if_on_line";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* L : *)Const "Line",
            Forall (App (App (Const "OnLine", Bvar 3 (* a *)), Bvar 0 (* L *)),
              Forall (App (App (Const "OnLine", Bvar 3 (* b *)), Bvar 1 (* L *)),
                Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 5 (* a *)), Bvar 4 (* b *))),
                  Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 3 (* L *)),
                    App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 7 (* a *)), Bvar 6 (* b *)), Bvar 5 (* c *))), Const "Zero")
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* area_add_if_between: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) ->
    (OnLine a L) -> (OnLine b L) -> (OnLine c L) ->
    (Not (Eq Point a b)) -> (Not (Eq Point b c)) -> (Not (Eq Point a c)) ->
    (Not (OnLine d L)) ->
    (Between a c b) ->
    (Eq Measure (Add (Area a c d) (Area d c b)) (Area a d b)) *)
  show_kterm "area_add_if_between";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 0 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 1 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 2 (* L *)),
                    Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 7 (* a *)), Bvar 6 (* b *))),
                      Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 7 (* b *)), Bvar 6 (* c *))),
                        Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 9 (* a *)), Bvar 7 (* c *))),
                          Forall (App (Const "Not", App (App (Const "OnLine", Bvar 7 (* d *)), Bvar 6 (* L *))),
                            Forall (App (App (App (Const "Between", Bvar 11 (* a *)), Bvar 9 (* c *)), Bvar 10 (* b *)),
                              App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (App (Const "Area", Bvar 12 (* a *)), Bvar 10 (* c *)), Bvar 9 (* d *))), App (App (App (Const "Area", Bvar 9 (* d *)), Bvar 10 (* c *)), Bvar 11 (* b *)))), App (App (App (Const "Area", Bvar 12 (* a *)), Bvar 9 (* d *)), Bvar 11 (* b *)))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* between_if_area_add: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) ->
    (OnLine a L) -> (OnLine b L) -> (OnLine c L) ->
    (Not (Eq Point a b)) -> (Not (Eq Point b c)) -> (Not (Eq Point a c)) ->
    (Not (OnLine d L)) ->
    (Eq Measure (Add (Area a c d) (Area d c b)) (Area a d b)) ->
    (Between a c b) *)
  show_kterm "between_if_area_add";
  [%expect
    {|
    Forall ((* a : *)Const "Point",
      Forall ((* b : *)Const "Point",
        Forall ((* c : *)Const "Point",
          Forall ((* d : *)Const "Point",
            Forall ((* L : *)Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4 (* a *)), Bvar 0 (* L *)),
                Forall (App (App (Const "OnLine", Bvar 4 (* b *)), Bvar 1 (* L *)),
                  Forall (App (App (Const "OnLine", Bvar 4 (* c *)), Bvar 2 (* L *)),
                    Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 7 (* a *)), Bvar 6 (* b *))),
                      Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 7 (* b *)), Bvar 6 (* c *))),
                        Forall (App (Const "Not", App (App (App (Const "Eq", Const "Point"), Bvar 9 (* a *)), Bvar 7 (* c *))),
                          Forall (App (Const "Not", App (App (Const "OnLine", Bvar 7 (* d *)), Bvar 6 (* L *))),
                            Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (App (Const "Area", Bvar 11 (* a *)), Bvar 9 (* c *)), Bvar 8 (* d *))), App (App (App (Const "Area", Bvar 8 (* d *)), Bvar 9 (* c *)), Bvar 10 (* b *)))), App (App (App (Const "Area", Bvar 11 (* a *)), Bvar 8 (* d *)), Bvar 10 (* b *))),
                              App (App (App (Const "Between", Bvar 12 (* a *)), Bvar 10 (* c *)), Bvar 11 (* b *))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    |}];

  (* Check kenv is empty at the end *)
  if Hashtbl.length kenv <> 0 then (
    Seq.iter print_endline (Hashtbl.to_seq_keys kenv);
    [%expect.unreachable])
