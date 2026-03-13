let kterm_to_repr (term : Kernel.Term.term) =
  let open Kernel.Term in
  let rec kterm_to_repr_helper (term : term) (indent : int) =
    let indent_str = String.make (indent * 2) ' ' in
    match term with
    | Const s -> Printf.sprintf "Const \"%s\"" s
    | Bvar n -> Printf.sprintf "Bvar %d" n
    | Fvar s -> Printf.sprintf "Fvar \"%s\"" s
    | Lam (ty, body) ->
        Printf.sprintf
          "Lam (%s,\n%s  %s\n%s)"
          (kterm_to_repr_helper ty indent)
          indent_str
          (kterm_to_repr_helper body (indent + 1))
          indent_str
    | Forall (ty, body) ->
        Printf.sprintf
          "Forall (%s,\n%s  %s\n%s)"
          (kterm_to_repr_helper ty indent)
          indent_str
          (kterm_to_repr_helper body (indent + 1))
          indent_str
    | App (f, arg) ->
        Printf.sprintf
          "App (%s, %s)"
          (kterm_to_repr_helper f indent)
          (kterm_to_repr_helper arg indent)
    | Sort n -> Printf.sprintf "Sort %d" n
  in
  kterm_to_repr_helper term 0

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
    let term = Hashtbl.find kenv name in
    let repr = kterm_to_repr term in
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
    Forall (Sort 1,
      Forall (Const "Empty",
        Bvar 1
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
    Forall (Sort 0,
      Forall (Const "False",
        Bvar 1
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
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
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
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        Forall (Bvar 1,
          Forall (App (Bvar 1, Bvar 0),
            App (App (Const "Exists", Bvar 3), Bvar 2)
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
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        Forall (Sort 0,
          Forall (App (App (Const "Exists", Bvar 2), Bvar 1),
            Forall (Forall (Bvar 3,
              Forall (App (Bvar 3, Bvar 0),
                Bvar 3
              )
            ),
              Bvar 2
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
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
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
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        Forall (Forall (Bvar 1,
          App (Bvar 1, Bvar 0)
        ),
          App (App (Const "Forall", Bvar 2), Bvar 1)
        )
      )
    )
    |}];

  (* Forall.elim : (A: Type) -> (p: A -> Prop) ->
      Forall A p -> (a: A) -> p a *)
  show_kterm "Forall.elim";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        Forall (App (App (Const "Forall", Bvar 1), Bvar 0),
          Forall (Bvar 2,
            App (Bvar 2, Bvar 0)
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
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Bvar 1,
          Forall (Bvar 1,
            App (App (Const "And", Bvar 3), Bvar 2)
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
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Sort 0,
          Forall (Forall (Bvar 2,
            Forall (Bvar 2,
              Bvar 2
            )
          ),
            Forall (App (App (Const "And", Bvar 3), Bvar 2),
              Bvar 2
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
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Bvar 1,
          App (App (Const "Or", Bvar 2), Bvar 1)
        )
      )
    )
    |}];

  (* Or.inr : (A : Prop) -> (B : Prop) -> B -> Or A B *)
  show_kterm "Or.inr";
  [%expect
    {|
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Bvar 0,
          App (App (Const "Or", Bvar 2), Bvar 1)
        )
      )
    )
    |}];

  (* Or.elim : (A : Prop) -> (B : Prop) -> (C : Prop) ->
      Or A B -> (A -> C) -> (B -> C) -> C *)
  show_kterm "Or.elim";
  [%expect
    {|
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Sort 0,
          Forall (App (App (Const "Or", Bvar 2), Bvar 1),
            Forall (Forall (Bvar 3,
              Bvar 2
            ),
              Forall (Forall (Bvar 3,
                Bvar 3
              ),
                Bvar 3
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

  (* Eq : (T: Type) -> T -> T -> Prop *)
  show_kterm "Eq";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (Bvar 1,
          Sort 0
        )
      )
    )
    |}];

  (* Eq.intro : (T: Type) -> (t: T) -> Eq T t t *)
  show_kterm "Eq.intro";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        App (App (App (Const "Eq", Bvar 1), Bvar 0), Bvar 0)
      )
    )
    |}];

  (* Eq.elim : (T: Type) -> (t: T) -> (motive : T -> Prop) -> (rfl: motive t) -> (t1: T) -> Eq T t t1 -> motive t1 *)
  show_kterm "Eq.elim";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (Forall (Bvar 1,
          Sort 0
        ),
          Forall (App (Bvar 0, Bvar 1),
            Forall (Bvar 3,
              Forall (App (App (App (Const "Eq", Bvar 4), Bvar 3), Bvar 0),
                App (Bvar 3, Bvar 1)
              )
            )
          )
        )
      )
    )
    |}];

  (* Ne : (A: Type) -> A -> A -> Prop *)
  show_kterm "Ne";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (Bvar 1,
          Sort 0
        )
      )
    )
    |}];
  
  (* Iff : Prop -> Prop -> Prop *)
  show_kterm "Iff";
  [%expect
    {|
    Forall (Sort 0,
      Forall (Sort 0,
        Sort 0
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
  [%expect {|
    Forall (Sort 1,
      App (Const "List", Bvar 0)
    )
    |}];

  (* List.cons : (A : Type) -> A -> List A -> List A *)
  show_kterm "List.cons";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (App (Const "List", Bvar 1),
          App (Const "List", Bvar 2)
        )
      )
    )
    |}];

  (* List.mem : (A : Type) -> A -> List A -> Prop *)
  show_kterm "List.mem";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (App (Const "List", Bvar 1),
          Sort 0
        )
      )
    )
    |}];

  (* List.not_mem_nil : (A : Type) -> (a : A) -> List.mem A a (List.nil A) -> False *)
  show_kterm "List.not_mem_nil";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (App (App (App (Const "List.mem", Bvar 1), Bvar 0), App (Const "List.nil", Bvar 1)),
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
    Forall (Sort 1,
      Forall (Bvar 0,
        Forall (Bvar 1,
          Forall (App (Const "List", Bvar 2),
            App (App (Const "And", Forall (App (App (App (Const "List.mem", Bvar 3), Bvar 2), App (App (App (Const "List.cons", Bvar 3), Bvar 1), Bvar 0)),
              App (App (Const "Or", App (App (App (Const "Eq", Bvar 4), Bvar 3), Bvar 2)), App (App (App (Const "List.mem", Bvar 4), Bvar 3), Bvar 1))
            )), Forall (App (App (Const "Or", App (App (App (Const "Eq", Bvar 3), Bvar 2), Bvar 1)), App (App (App (Const "List.mem", Bvar 3), Bvar 2), Bvar 0)),
              App (App (App (Const "List.mem", Bvar 4), Bvar 3), App (App (App (Const "List.cons", Bvar 4), Bvar 2), Bvar 1))
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
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        Forall (App (Const "List", Bvar 1),
          Sort 0
        )
      )
    )
    |}];

  (* List.forall_nil : (A : Type) -> (p : A -> Prop) -> List.forall A p (List.nil A) *)
  show_kterm "List.forall_nil";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        App (App (App (Const "List.forall", Bvar 1), Bvar 0), App (Const "List.nil", Bvar 1))
      )
    )
    |}];

  (* List.forall_cons : (A : Type) -> (p : A -> Prop) -> (a : A) -> (L : List A) ->
    And (List.forall A p (List.cons A a L) -> And (p a) (List.forall A p L))
        (And (p a) (List.forall A p L) -> List.forall A p (List.cons A a L)) *)
  show_kterm "List.forall_cons";
  [%expect
    {|
    Forall (Sort 1,
      Forall (Forall (Bvar 0,
        Sort 0
      ),
        Forall (Bvar 1,
          Forall (App (Const "List", Bvar 2),
            App (App (Const "And", Forall (App (App (App (Const "List.forall", Bvar 3), Bvar 2), App (App (App (Const "List.cons", Bvar 3), Bvar 1), Bvar 0)),
              App (App (Const "And", App (Bvar 3, Bvar 2)), App (App (App (Const "List.forall", Bvar 4), Bvar 3), Bvar 1))
            )), Forall (App (App (Const "And", App (Bvar 2, Bvar 1)), App (App (App (Const "List.forall", Bvar 3), Bvar 2), Bvar 0)),
              App (App (App (Const "List.forall", Bvar 4), Bvar 3), App (App (App (Const "List.cons", Bvar 4), Bvar 2), Bvar 1))
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
    Forall (Const "Measure",
      Forall (App (App (Const "Lt", Bvar 0), Bvar 0),
        Const "False"
      )
    )
    |}];

  (* LtTrans : (a: Measure) -> (b: Measure) -> (c: Measure) -> Lt a b -> Lt b c -> Lt a c *)
  show_kterm "LtTrans";
  [%expect
    {|
    Forall (Const "Measure",
      Forall (Const "Measure",
        Forall (Const "Measure",
          Forall (App (App (Const "Lt", Bvar 2), Bvar 1),
            Forall (App (App (Const "Lt", Bvar 2), Bvar 1),
              App (App (Const "Lt", Bvar 4), Bvar 2)
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
    Forall (Const "Measure",
      Forall (Const "Measure",
        App (App (Const "Or", App (App (Const "Lt", Bvar 1), Bvar 0)), App (App (Const "Or", App (App (Const "Lt", Bvar 0), Bvar 1)), App (App (App (Const "Eq", Const "Measure"), Bvar 1), Bvar 0)))
      )
    )
    |}];

  (* LtAntisymm : (a: Measure) -> (b: Measure) -> Lt a b -> Lt b a -> False *)
  show_kterm "LtAntisymm";
  [%expect
    {|
    Forall (Const "Measure",
      Forall (Const "Measure",
        Forall (App (App (Const "Lt", Bvar 1), Bvar 0),
          Forall (App (App (Const "Lt", Bvar 1), Bvar 2),
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
    Forall (Const "Measure",
      App (App (Const "Or", App (App (Const "Lt", Const "Zero"), Bvar 0)), App (App (App (Const "Eq", Const "Measure"), Const "Zero"), Bvar 0))
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
    Forall (Const "Measure",
      Forall (Const "Measure",
        App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", Bvar 1), Bvar 0)), App (App (Const "Add", Bvar 0), Bvar 1))
      )
    )
    |}];

  (* AddAssoc : (a: Measure) -> (b: Measure) -> (c: Measure) -> Eq Measure (Add (Add a b) c) (Add a (Add b c)) *)
  show_kterm "AddAssoc";
  [%expect
    {|
    Forall (Const "Measure",
      Forall (Const "Measure",
        Forall (Const "Measure",
          App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (Const "Add", Bvar 2), Bvar 1)), Bvar 0)), App (App (Const "Add", Bvar 2), App (App (Const "Add", Bvar 1), Bvar 0)))
        )
      )
    )
    |}];

  (* AddZero : (a: Measure) -> Eq Measure (Add a Zero) a *)
  show_kterm "AddZero";
  [%expect
    {|
    Forall (Const "Measure",
      App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", Bvar 0), Const "Zero")), Bvar 0)
    )
    |}];

  (* LtAdd : (a: Measure) -> (b: Measure) -> (c: Measure) -> Lt a b -> Lt (Add a c) (Add b c) *)
  show_kterm "LtAdd";
  [%expect
    {|
    Forall (Const "Measure",
      Forall (Const "Measure",
        Forall (Const "Measure",
          Forall (App (App (Const "Lt", Bvar 2), Bvar 1),
            App (App (Const "Lt", App (App (Const "Add", Bvar 3), Bvar 1)), App (App (Const "Add", Bvar 2), Bvar 1))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Const "Measure"
      )
    )
    |}];

  (* Angle : (a: Point) -> (b: Point) -> (c: Point) -> Measure *)
  show_kterm "Angle";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Const "Measure"
        )
      )
    )
    |}];

  (* Area : (a: Point) -> (b: Point) -> (c: Point) -> Measure *)
  show_kterm "Area";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
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

  (* pt_exists :
    (p_list : List Point) -> (l_list : List Line) -> (c_list : List Circle) ->
    Exists Point (fun (a : Point) => distinct_from a p_list l_list c_list) *)
  show_kterm "pt_exists";
  [%expect
    {|
    Forall (App (Const "List", Const "Point"),
      Forall (App (Const "List", Const "Line"),
        Forall (App (Const "List", Const "Circle"),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 3),
              Const "False"
            )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
              Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                Const "False"
              )
            )), Bvar 2))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
              Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                Const "False"
              )
            )), Bvar 1))
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
    Forall (Const "Line",
      Forall (App (Const "List", Const "Point"),
        Forall (App (Const "List", Const "Line"),
          Forall (App (Const "List", Const "Circle"),
            Forall (Forall (App (App (App (Const "List.mem", Const "Line"), Bvar 3), Bvar 1),
              Const "False"
            ),
              App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 5)), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 4),
                  Const "False"
                )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                    Const "False"
                  )
                )), Bvar 3))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                  Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                    Const "False"
                  )
                )), Bvar 2)))
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
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (Const "List", Const "Point"),
            Forall (App (Const "List", Const "Line"),
              Forall (App (Const "List", Const "Circle"),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 5),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 6),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 6), Bvar 5),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "List.mem", Const "Line"), Bvar 8), Bvar 4),
                        Const "False"
                      ),
                        App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                          App (App (Const "And", App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 10)), App (App (App (Const "Between", Bvar 9), Bvar 0), Bvar 8))), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 7),
                            Const "False"
                          )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                            Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                              Const "False"
                            )
                          )), Bvar 6))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                            Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                              Const "False"
                            )
                          )), Bvar 5)))
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
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (Const "List", Const "Point"),
            Forall (App (Const "List", Const "Line"),
              Forall (App (Const "List", Const "Circle"),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 5),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 6),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 6), Bvar 5),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "List.mem", Const "Line"), Bvar 8), Bvar 4),
                        Const "False"
                      ),
                        App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                          App (App (Const "And", App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 10)), App (App (App (Const "Between", Bvar 9), Bvar 8), Bvar 0))), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 7),
                            Const "False"
                          )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                            Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                              Const "False"
                            )
                          )), Bvar 6))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                            Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                              Const "False"
                            )
                          )), Bvar 5)))
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
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (App (Const "List", Const "Point"),
          Forall (App (Const "List", Const "Line"),
            Forall (App (Const "List", Const "Circle"),
              Forall (Forall (App (App (Const "OnLine", Bvar 3), Bvar 4),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                  App (App (Const "And", App (App (App (Const "SameSide", Bvar 0), Bvar 5), Bvar 6)), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 4),
                    Const "False"
                  )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                      Const "False"
                    )
                  )), Bvar 3))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                    Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                      Const "False"
                    )
                  )), Bvar 2)))
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
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (App (Const "List", Const "Point"),
          Forall (App (Const "List", Const "Line"),
            Forall (App (Const "List", Const "Circle"),
              Forall (Forall (App (App (Const "OnLine", Bvar 3), Bvar 4),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                  App (App (Const "And", App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0), Bvar 6),
                    Const "False"
                  )), Forall (App (App (App (Const "SameSide", Bvar 0), Bvar 5), Bvar 6),
                    Const "False"
                  ))), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 4),
                    Const "False"
                  )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                      Const "False"
                    )
                  )), Bvar 3))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                    Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                      Const "False"
                    )
                  )), Bvar 2)))
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
    Forall (Const "Circle",
      Forall (App (Const "List", Const "Point"),
        Forall (App (Const "List", Const "Line"),
          Forall (App (Const "List", Const "Circle"),
            Forall (Forall (App (App (App (Const "List.mem", Const "Circle"), Bvar 3), Bvar 0),
              Const "False"
            ),
              App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 5)), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 4),
                  Const "False"
                )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                    Const "False"
                  )
                )), Bvar 3))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                  Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                    Const "False"
                  )
                )), Bvar 2)))
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
    Forall (Const "Circle",
      Forall (App (Const "List", Const "Point"),
        Forall (App (Const "List", Const "Line"),
          Forall (App (Const "List", Const "Circle"),
            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
              App (App (Const "And", App (App (Const "InCircle", Bvar 0), Bvar 4)), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 3),
                Const "False"
              )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                  Const "False"
                )
              )), Bvar 2))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                  Const "False"
                )
              )), Bvar 1)))
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
    Forall (Const "Circle",
      Forall (App (Const "List", Const "Point"),
        Forall (App (Const "List", Const "Line"),
          Forall (App (Const "List", Const "Circle"),
            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
              App (App (Const "And", App (App (Const "And", Forall (App (App (Const "OnCircle", Bvar 0), Bvar 4),
                Const "False"
              )), Forall (App (App (Const "InCircle", Bvar 0), Bvar 4),
                Const "False"
              ))), App (App (Const "And", App (App (Const "And", Forall (App (App (App (Const "List.mem", Const "Point"), Bvar 0), Bvar 3),
                Const "False"
              )), App (App (App (Const "List.forall", Const "Line"), Lam (Const "Line",
                Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
                  Const "False"
                )
              )), Bvar 2))), App (App (App (Const "List.forall", Const "Circle"), Lam (Const "Circle",
                Forall (App (App (Const "OnCircle", Bvar 1), Bvar 0),
                  Const "False"
                )
              )), Bvar 1)))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1), Bvar 0),
          Const "False"
        ),
          App (App (Const "Exists", Const "Line"), Lam (Const "Line",
            App (App (Const "And", App (App (Const "OnLine", Bvar 3), Bvar 0)), App (App (Const "OnLine", Bvar 2), Bvar 0))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1), Bvar 0),
          Const "False"
        ),
          App (App (Const "Exists", Const "Circle"), Lam (Const "Circle",
            App (App (Const "And", App (App (Const "CenterCircle", Bvar 3), Bvar 0)), App (App (Const "OnCircle", Bvar 2), Bvar 0))
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
    Forall (Const "Line",
      Forall (Const "Line",
        Forall (App (App (Const "LinesInter", Bvar 1), Bvar 0),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 3)), App (App (Const "OnLine", Bvar 0), Bvar 2))
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
    Forall (Const "Line",
      Forall (Const "Circle",
        Forall (App (App (Const "LineCircleInter", Bvar 1), Bvar 0),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 3)), App (App (Const "OnCircle", Bvar 0), Bvar 2))
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
    Forall (Const "Line",
      Forall (Const "Circle",
        Forall (App (App (Const "LineCircleInter", Bvar 1), Bvar 0),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1), Bvar 0),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnLine", Bvar 1), Bvar 4)), App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 4)), App (App (Const "And", App (App (Const "OnCircle", Bvar 1), Bvar 3)), App (App (Const "OnCircle", Bvar 0), Bvar 3)))))
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
    Forall (Const "Line",
      Forall (Const "Circle",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (App (App (Const "OnLine", Bvar 1), Bvar 3),
              Forall (App (App (Const "OnLine", Bvar 1), Bvar 4),
                Forall (App (App (Const "InCircle", Bvar 3), Bvar 4),
                  Forall (Forall (App (App (Const "OnCircle", Bvar 3), Bvar 5),
                    Const "False"
                  ),
                    Forall (Forall (App (App (Const "InCircle", Bvar 4), Bvar 6),
                      Const "False"
                    ),
                      App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                        App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 9)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 8)), App (App (App (Const "Between", Bvar 7), Bvar 0), Bvar 6)))
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
    Forall (Const "Line",
      Forall (Const "Circle",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (App (App (Const "OnLine", Bvar 1), Bvar 3),
              Forall (App (App (Const "OnLine", Bvar 1), Bvar 4),
                Forall (App (App (Const "InCircle", Bvar 3), Bvar 4),
                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 4),
                    Const "False"
                  ),
                    App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                      App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 8)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 7)), App (App (App (Const "Between", Bvar 0), Bvar 6), Bvar 5)))
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
    Forall (Const "Circle",
      Forall (Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1), Bvar 0),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 3)), App (App (Const "OnCircle", Bvar 0), Bvar 2))
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
    Forall (Const "Circle",
      Forall (Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1), Bvar 0),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1), Bvar 0),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 1), Bvar 4)), App (App (Const "And", App (App (Const "OnCircle", Bvar 1), Bvar 3)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 4)), App (App (Const "OnCircle", Bvar 0), Bvar 3)))))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Const "Circle",
              Forall (Const "Circle",
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                    Forall (Forall (App (App (Const "OnLine", Bvar 7), Bvar 4),
                      Const "False"
                    ),
                      Forall (App (App (Const "CenterCircle", Bvar 7), Bvar 4),
                        Forall (App (App (Const "CenterCircle", Bvar 7), Bvar 4),
                          Forall (App (App (Const "CirclesInter", Bvar 6), Bvar 5),
                            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                              App (App (Const "And", App (App (App (Const "SameSide", Bvar 0), Bvar 12), Bvar 9)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 8)), App (App (Const "OnCircle", Bvar 0), Bvar 7)))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Const "Circle",
              Forall (Const "Circle",
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                    Forall (Forall (App (App (Const "OnLine", Bvar 7), Bvar 4),
                      Const "False"
                    ),
                      Forall (App (App (Const "CenterCircle", Bvar 7), Bvar 4),
                        Forall (App (App (Const "CenterCircle", Bvar 7), Bvar 4),
                          Forall (App (App (Const "CirclesInter", Bvar 6), Bvar 5),
                            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                              App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0), Bvar 9),
                                Const "False"
                              )), App (App (Const "And", Forall (App (App (App (Const "SameSide", Bvar 0), Bvar 12), Bvar 9),
                                Const "False"
                              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 8)), App (App (Const "OnCircle", Bvar 0), Bvar 7))))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Line",
          Forall (Const "Line",
            Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 2),
              Const "False"
            ),
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                  Forall (App (App (Const "OnLine", Bvar 6), Bvar 3),
                    Forall (App (App (Const "OnLine", Bvar 6), Bvar 4),
                      App (App (App (Const "Eq", Const "Line"), Bvar 6), Bvar 5)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Circle",
          Forall (App (App (Const "CenterCircle", Bvar 2), Bvar 0),
            Forall (App (App (Const "CenterCircle", Bvar 2), Bvar 1),
              App (App (App (Const "Eq", Const "Point"), Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Circle",
        Forall (App (App (Const "CenterCircle", Bvar 1), Bvar 0),
          App (App (Const "InCircle", Bvar 2), Bvar 1)
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
    Forall (Const "Point",
      Forall (Const "Circle",
        Forall (App (App (Const "InCircle", Bvar 1), Bvar 0),
          Forall (App (App (Const "OnCircle", Bvar 2), Bvar 1),
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (App (App (Const "Between", Bvar 2), Bvar 1), Bvar 0),
            App (App (Const "And", App (App (App (Const "Between", Bvar 1), Bvar 2), Bvar 3)), App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 2),
              Const "False"
            )), App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 1),
              Const "False"
            )), Forall (App (App (App (Const "Between", Bvar 2), Bvar 3), Bvar 1),
              Const "False"
            ))))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  App (App (Const "OnLine", Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                Forall (App (App (Const "OnLine", Bvar 3), Bvar 2),
                  App (App (Const "OnLine", Bvar 5), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (App (Const "Between", Bvar 4), Bvar 1), Bvar 3),
                App (App (App (Const "Between", Bvar 5), Bvar 2), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
                App (App (App (Const "Between", Bvar 5), Bvar 4), Bvar 2)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (Const "OnLine", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnLine", Bvar 3), Bvar 1),
                Forall (App (App (Const "OnLine", Bvar 3), Bvar 2),
                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 6), Bvar 5),
                    Const "False"
                  ),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 6), Bvar 5),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 8), Bvar 6),
                        Const "False"
                      ),
                        App (App (Const "Or", App (App (App (Const "Between", Bvar 9), Bvar 8), Bvar 7)), App (App (Const "Or", App (App (App (Const "Between", Bvar 8), Bvar 9), Bvar 7)), App (App (App (Const "Between", Bvar 9), Bvar 7), Bvar 8)))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (App (Const "Between", Bvar 4), Bvar 3), Bvar 1),
                Forall (App (App (App (Const "Between", Bvar 3), Bvar 4), Bvar 2),
                  Const "False"
                )
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
    Forall (Const "Point",
      Forall (Const "Line",
        Forall (Forall (App (App (Const "OnLine", Bvar 1), Bvar 0),
          Const "False"
        ),
          App (App (App (Const "SameSide", Bvar 2), Bvar 2), Bvar 1)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Line",
          Forall (App (App (App (Const "SameSide", Bvar 2), Bvar 1), Bvar 0),
            App (App (App (Const "SameSide", Bvar 2), Bvar 3), Bvar 1)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Line",
          Forall (App (App (App (Const "SameSide", Bvar 2), Bvar 1), Bvar 0),
            Forall (App (App (Const "OnLine", Bvar 3), Bvar 1),
              Const "False"
            )
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (App (Const "SameSide", Bvar 3), Bvar 2), Bvar 0),
              Forall (App (App (App (Const "SameSide", Bvar 4), Bvar 2), Bvar 1),
                App (App (App (Const "SameSide", Bvar 4), Bvar 3), Bvar 2)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Forall (App (App (Const "OnLine", Bvar 3), Bvar 0),
              Const "False"
            ),
              Forall (Forall (App (App (Const "OnLine", Bvar 3), Bvar 1),
                Const "False"
              ),
                Forall (Forall (App (App (Const "OnLine", Bvar 3), Bvar 2),
                  Const "False"
                ),
                  Forall (Forall (App (App (App (Const "SameSide", Bvar 6), Bvar 5), Bvar 3),
                    Const "False"
                  ),
                    App (App (Const "Or", App (App (App (Const "SameSide", Bvar 7), Bvar 5), Bvar 4)), App (App (App (Const "SameSide", Bvar 6), Bvar 5), Bvar 4))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (App (Const "SameSide", Bvar 4), Bvar 2), Bvar 1),
                App (App (App (Const "SameSide", Bvar 5), Bvar 4), Bvar 2)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                Forall (Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  Const "False"
                ),
                  App (App (App (Const "SameSide", Bvar 5), Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (App (Const "Between", Bvar 3), Bvar 2), Bvar 1),
              Forall (App (App (Const "OnLine", Bvar 3), Bvar 1),
                Forall (App (App (App (Const "SameSide", Bvar 5), Bvar 3), Bvar 2),
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Const "Line",
              Forall (Forall (App (App (App (Const "Eq", Const "Line"), Bvar 1), Bvar 0),
                Const "False"
              ),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  Forall (App (App (Const "OnLine", Bvar 5), Bvar 2),
                    Forall (App (App (Const "OnLine", Bvar 7), Bvar 3),
                      Forall (App (App (Const "OnLine", Bvar 6), Bvar 4),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 8),
                          Const "False"
                        ),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 8), Bvar 9),
                            Const "False"
                          ),
                            Forall (Forall (App (App (App (Const "SameSide", Bvar 11), Bvar 9), Bvar 8),
                              Const "False"
                            ),
                              App (App (App (Const "Between", Bvar 12), Bvar 11), Bvar 10)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (Const "Line",
                Forall (Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 6), Bvar 2),
                    Forall (App (App (Const "OnLine", Bvar 7), Bvar 2),
                      Forall (App (App (Const "OnLine", Bvar 8), Bvar 2),
                        Forall (App (App (Const "OnLine", Bvar 8), Bvar 5),
                          Forall (App (App (Const "OnLine", Bvar 8), Bvar 5),
                            Forall (App (App (Const "OnLine", Bvar 8), Bvar 5),
                              Forall (App (App (App (Const "SameSide", Bvar 10), Bvar 9), Bvar 8),
                                Forall (App (App (App (Const "SameSide", Bvar 12), Bvar 11), Bvar 7),
                                  Forall (App (App (App (Const "SameSide", Bvar 13), Bvar 11), Bvar 9),
                                    Const "False"
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (Const "Line",
                Forall (Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 6), Bvar 2),
                    Forall (App (App (Const "OnLine", Bvar 7), Bvar 2),
                      Forall (App (App (Const "OnLine", Bvar 8), Bvar 2),
                        Forall (App (App (Const "OnLine", Bvar 8), Bvar 5),
                          Forall (App (App (Const "OnLine", Bvar 8), Bvar 5),
                            Forall (App (App (Const "OnLine", Bvar 8), Bvar 5),
                              Forall (App (App (App (Const "SameSide", Bvar 10), Bvar 9), Bvar 8),
                                Forall (Forall (App (App (App (Const "SameSide", Bvar 12), Bvar 10), Bvar 8),
                                  Const "False"
                                ),
                                  Forall (Forall (App (App (Const "OnLine", Bvar 11), Bvar 9),
                                    Const "False"
                                  ),
                                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 14), Bvar 15),
                                      Const "False"
                                    ),
                                      App (App (App (Const "SameSide", Bvar 15), Bvar 14), Bvar 10)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Line",
                Forall (Const "Line",
                  Forall (Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 7), Bvar 2),
                      Forall (App (App (Const "OnLine", Bvar 8), Bvar 2),
                        Forall (App (App (Const "OnLine", Bvar 9), Bvar 2),
                          Forall (App (App (Const "OnLine", Bvar 9), Bvar 5),
                            Forall (App (App (Const "OnLine", Bvar 9), Bvar 5),
                              Forall (App (App (Const "OnLine", Bvar 9), Bvar 5),
                                Forall (App (App (App (Const "SameSide", Bvar 11), Bvar 10), Bvar 8),
                                  Forall (App (App (App (Const "SameSide", Bvar 13), Bvar 12), Bvar 7),
                                    Forall (App (App (App (Const "SameSide", Bvar 12), Bvar 11), Bvar 9),
                                      Forall (App (App (App (Const "SameSide", Bvar 14), Bvar 12), Bvar 9),
                                        App (App (App (Const "SameSide", Bvar 15), Bvar 13), Bvar 12)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Const "Circle",
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                    Forall (App (App (Const "InCircle", Bvar 7), Bvar 3),
                      Forall (App (App (Const "OnCircle", Bvar 7), Bvar 4),
                        Forall (App (App (Const "OnCircle", Bvar 7), Bvar 5),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 8),
                            Const "False"
                          ),
                            App (App (App (Const "Between", Bvar 10), Bvar 11), Bvar 9)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3), Bvar 0)), App (App (Const "OnCircle", Bvar 3), Bvar 0)),
              Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3), Bvar 1)), App (App (Const "OnCircle", Bvar 3), Bvar 1)),
                Forall (App (App (App (Const "Between", Bvar 5), Bvar 3), Bvar 4),
                  App (App (Const "InCircle", Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3), Bvar 0)), App (App (Const "OnCircle", Bvar 3), Bvar 0)),
              Forall (Forall (App (App (Const "InCircle", Bvar 2), Bvar 1),
                Const "False"
              ),
                Forall (App (App (App (Const "Between", Bvar 5), Bvar 3), Bvar 4),
                  App (App (Const "And", Forall (App (App (Const "InCircle", Bvar 5), Bvar 3),
                    Const "False"
                  )), Forall (App (App (Const "OnCircle", Bvar 5), Bvar 3),
                    Const "False"
                  ))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (Const "Circle",
                Forall (Const "Circle",
                  Forall (Forall (App (App (App (Const "Eq", Const "Circle"), Bvar 1), Bvar 0),
                    Const "False"
                  ),
                    Forall (App (App (Const "OnCircle", Bvar 5), Bvar 2),
                      Forall (App (App (Const "OnCircle", Bvar 6), Bvar 2),
                        Forall (App (App (Const "OnCircle", Bvar 6), Bvar 4),
                          Forall (App (App (Const "OnCircle", Bvar 7), Bvar 4),
                            Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 8),
                              Const "False"
                            ),
                              Forall (App (App (Const "CenterCircle", Bvar 12), Bvar 7),
                                Forall (App (App (Const "CenterCircle", Bvar 12), Bvar 7),
                                  Forall (App (App (Const "OnLine", Bvar 14), Bvar 10),
                                    Forall (App (App (Const "OnLine", Bvar 14), Bvar 11),
                                      Forall (App (App (App (Const "SameSide", Bvar 14), Bvar 13), Bvar 12),
                                        Const "False"
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

  (* lines_inter_if_diff_sides: (a : Point) -> (b : Point) -> (L : Line) -> (M : Line) ->
    (Not (SameSide a b L)) ->
    (OnLine a M) ->
    (OnLine b M) ->
    (LinesInter L M) *)
  show_kterm "lines_inter_if_diff_sides";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Line",
          Forall (Const "Line",
            Forall (Forall (App (App (App (Const "SameSide", Bvar 3), Bvar 2), Bvar 1),
              Const "False"
            ),
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                  App (App (Const "LinesInter", Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Line",
          Forall (Const "Circle",
            Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3), Bvar 0)), App (App (Const "OnCircle", Bvar 3), Bvar 0)),
              Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3), Bvar 1)), App (App (Const "OnCircle", Bvar 3), Bvar 1)),
                Forall (Forall (App (App (App (Const "SameSide", Bvar 5), Bvar 4), Bvar 3),
                  Const "False"
                ),
                  App (App (Const "LineCircleInter", Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Line",
        Forall (Const "Circle",
          Forall (App (App (Const "InCircle", Bvar 2), Bvar 0),
            Forall (App (App (Const "OnLine", Bvar 3), Bvar 2),
              App (App (Const "LineCircleInter", Bvar 3), Bvar 2)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Circle",
          Forall (Const "Circle",
            Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
              Forall (App (App (Const "Or", App (App (Const "InCircle", Bvar 3), Bvar 2)), App (App (Const "OnCircle", Bvar 3), Bvar 2)),
                Forall (App (App (Const "InCircle", Bvar 5), Bvar 2),
                  Forall (App (App (Const "And", Forall (App (App (Const "InCircle", Bvar 5), Bvar 3),
                    Const "False"
                  )), Forall (App (App (Const "OnCircle", Bvar 5), Bvar 3),
                    Const "False"
                  )),
                    App (App (Const "CirclesInter", Bvar 5), Bvar 4)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Circle",
          Forall (Const "Circle",
            Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
              Forall (App (App (Const "InCircle", Bvar 3), Bvar 2),
                Forall (App (App (Const "InCircle", Bvar 5), Bvar 2),
                  Forall (App (App (Const "OnCircle", Bvar 5), Bvar 3),
                    App (App (Const "CirclesInter", Bvar 5), Bvar 4)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 1), Bvar 0)), Const "Zero"),
          App (App (App (Const "Eq", Const "Point"), Bvar 2), Bvar 1)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1), Bvar 0),
          App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 2), Bvar 1)), Const "Zero")
        )
      )
    )
    |}];

  (* length_nonneg: (a : Point) -> (b : Point) ->
    (Not (Lt (Length a b) Zero)) *)
  show_kterm "length_nonneg";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (App (App (Const "Lt", App (App (Const "Length", Bvar 1), Bvar 0)), Const "Zero"),
          Const "False"
        )
      )
    )
    |}];

  (* length_symm: (a : Point) -> (b : Point) ->
    (Eq Measure (Length a b) (Length b a)) *)
  show_kterm "length_symm";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 1), Bvar 0)), App (App (Const "Length", Bvar 0), Bvar 1))
      )
    )
    |}];

  (* angle_symm: (a : Point) -> (b : Point) -> (c : Point) ->
    (Not (Eq Point a b)) -> (Not (Eq Point b c)) ->
    (Eq Measure (Angle a b c) (Angle c b a)) *)
  show_kterm "angle_symm";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 2), Bvar 1),
            Const "False"
          ),
            Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 2), Bvar 1),
              Const "False"
            ),
              App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 4), Bvar 3), Bvar 2)), App (App (App (Const "Angle", Bvar 2), Bvar 3), Bvar 4))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Forall (App (App (Const "Lt", App (App (App (Const "Angle", Bvar 2), Bvar 1), Bvar 0)), Const "Zero"),
            Const "False"
          ),
            Forall (App (App (Const "Lt", App (App (Const "Add", Const "RightAngle"), Const "RightAngle")), App (App (App (Const "Angle", Bvar 3), Bvar 2), Bvar 1)),
              Const "False"
            )
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
    Forall (Const "Point",
      Forall (Const "Point",
        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 1), Bvar 1), Bvar 0)), Const "Zero")
      )
    )
    |}];

  (* area_nonneg: (a : Point) -> (b : Point) -> (c : Point) ->
    (Not (Lt (Area a b c) Zero)) *)
  show_kterm "area_nonneg";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (App (Const "Lt", App (App (App (Const "Area", Bvar 2), Bvar 1), Bvar 0)), Const "Zero"),
            Const "False"
          )
        )
      )
    )
    |}];

  (* area_perm: (a : Point) -> (b : Point) -> (c : Point) ->
    (And (Eq Measure (Area a b c) (Area c a b)) (Eq Measure (Area a b c) (Area a c b))) *)
  show_kterm "area_perm";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 2), Bvar 1), Bvar 0)), App (App (App (Const "Area", Bvar 0), Bvar 2), Bvar 1))), App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 2), Bvar 1), Bvar 0)), App (App (App (Const "Area", Bvar 2), Bvar 0), Bvar 1)))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Point",
                Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 5), Bvar 4)), App (App (Const "Length", Bvar 2), Bvar 1)),
                  Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 5), Bvar 4)), App (App (Const "Length", Bvar 2), Bvar 1)),
                    Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 7), Bvar 6), Bvar 5)), App (App (App (Const "Angle", Bvar 4), Bvar 3), Bvar 2)),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 7), Bvar 6), Bvar 8)), App (App (App (Const "Angle", Bvar 4), Bvar 3), Bvar 5)),
                        Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 7), Bvar 9), Bvar 8)), App (App (App (Const "Angle", Bvar 4), Bvar 6), Bvar 5)),
                          App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 10), Bvar 9), Bvar 8)), App (App (App (Const "Area", Bvar 7), Bvar 6), Bvar 5))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (App (App (Const "Between", Bvar 2), Bvar 1), Bvar 0),
            App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (Const "Length", Bvar 3), Bvar 2)), App (App (Const "Length", Bvar 2), Bvar 1))), App (App (Const "Length", Bvar 3), Bvar 1))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (Const "Circle",
              Forall (App (App (Const "CenterCircle", Bvar 4), Bvar 1),
                Forall (App (App (Const "CenterCircle", Bvar 5), Bvar 1),
                  Forall (App (App (Const "OnCircle", Bvar 5), Bvar 3),
                    Forall (App (App (Const "OnCircle", Bvar 5), Bvar 3),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 8), Bvar 7)), App (App (Const "Length", Bvar 8), Bvar 6)),
                        App (App (App (Const "Eq", Const "Circle"), Bvar 6), Bvar 5)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 5), Bvar 3)), App (App (Const "Length", Bvar 5), Bvar 4)),
                  App (App (Const "OnCircle", Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                Forall (App (App (Const "OnCircle", Bvar 3), Bvar 2),
                  App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 6), Bvar 4)), App (App (Const "Length", Bvar 6), Bvar 5))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                Forall (App (App (Const "Lt", App (App (Const "Length", Bvar 5), Bvar 3)), App (App (Const "Length", Bvar 5), Bvar 4)),
                  App (App (Const "InCircle", Bvar 4), Bvar 3)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                Forall (App (App (Const "InCircle", Bvar 3), Bvar 2),
                  App (App (Const "Lt", App (App (Const "Length", Bvar 6), Bvar 4)), App (App (Const "Length", Bvar 6), Bvar 5))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 2),
              Const "False"
            ),
              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 4), Bvar 2),
                Const "False"
              ),
                Forall (App (App (Const "OnLine", Bvar 5), Bvar 2),
                  Forall (App (App (Const "OnLine", Bvar 5), Bvar 3),
                    Forall (App (App (Const "OnLine", Bvar 5), Bvar 4),
                      Forall (Forall (App (App (App (Const "Between", Bvar 7), Bvar 8), Bvar 6),
                        Const "False"
                      ),
                        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 8), Bvar 9), Bvar 7)), Const "Zero")
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 2),
              Const "False"
            ),
              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 4), Bvar 2),
                Const "False"
              ),
                Forall (App (App (Const "OnLine", Bvar 5), Bvar 2),
                  Forall (App (App (Const "OnLine", Bvar 5), Bvar 3),
                    Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 6), Bvar 7), Bvar 5)), Const "Zero"),
                      App (App (Const "And", App (App (Const "OnLine", Bvar 6), Bvar 5)), Forall (App (App (App (Const "Between", Bvar 7), Bvar 8), Bvar 6),
                        Const "False"
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (Const "Line",
                Forall (App (App (Const "OnLine", Bvar 5), Bvar 1),
                  Forall (App (App (Const "OnLine", Bvar 6), Bvar 1),
                    Forall (App (App (Const "OnLine", Bvar 6), Bvar 3),
                      Forall (App (App (Const "OnLine", Bvar 6), Bvar 3),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 8),
                          Const "False"
                        ),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 10), Bvar 8),
                            Const "False"
                          ),
                            Forall (Forall (App (App (Const "OnLine", Bvar 8), Bvar 7),
                              Const "False"
                            ),
                              Forall (Forall (App (App (Const "OnLine", Bvar 9), Bvar 7),
                                Const "False"
                              ),
                                Forall (Forall (App (App (App (Const "Eq", Const "Line"), Bvar 9), Bvar 8),
                                  Const "False"
                                ),
                                  Forall (App (App (App (Const "SameSide", Bvar 13), Bvar 11), Bvar 9),
                                    Forall (App (App (App (Const "SameSide", Bvar 13), Bvar 12), Bvar 11),
                                      App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 15), Bvar 16), Bvar 14)), App (App (Const "Add", App (App (App (Const "Angle", Bvar 15), Bvar 16), Bvar 13)), App (App (App (Const "Angle", Bvar 13), Bvar 16), Bvar 14)))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (Const "Line",
                Forall (App (App (Const "OnLine", Bvar 5), Bvar 1),
                  Forall (App (App (Const "OnLine", Bvar 6), Bvar 1),
                    Forall (App (App (Const "OnLine", Bvar 6), Bvar 3),
                      Forall (App (App (Const "OnLine", Bvar 6), Bvar 3),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 8),
                          Const "False"
                        ),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 10), Bvar 8),
                            Const "False"
                          ),
                            Forall (Forall (App (App (Const "OnLine", Bvar 8), Bvar 7),
                              Const "False"
                            ),
                              Forall (Forall (App (App (Const "OnLine", Bvar 9), Bvar 7),
                                Const "False"
                              ),
                                Forall (Forall (App (App (App (Const "Eq", Const "Line"), Bvar 9), Bvar 8),
                                  Const "False"
                                ),
                                  Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 13), Bvar 14), Bvar 12)), App (App (Const "Add", App (App (App (Const "Angle", Bvar 13), Bvar 14), Bvar 11)), App (App (App (Const "Angle", Bvar 11), Bvar 14), Bvar 12))),
                                    App (App (Const "And", App (App (App (Const "SameSide", Bvar 14), Bvar 12), Bvar 10)), App (App (App (Const "SameSide", Bvar 13), Bvar 12), Bvar 11))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 0),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                  Forall (App (App (App (Const "Between", Bvar 6), Bvar 4), Bvar 5),
                    Forall (Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                      Const "False"
                    ),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 8), Bvar 6), Bvar 5)), App (App (App (Const "Angle", Bvar 5), Bvar 6), Bvar 7)),
                        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 9), Bvar 7), Bvar 6)), Const "RightAngle")
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 0),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                  Forall (App (App (App (Const "Between", Bvar 6), Bvar 4), Bvar 5),
                    Forall (Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                      Const "False"
                    ),
                      Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 8), Bvar 6), Bvar 5)), Const "RightAngle"),
                        App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 9), Bvar 7), Bvar 6)), App (App (App (Const "Angle", Bvar 6), Bvar 7), Bvar 8))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Line",
                Forall (Const "Line",
                  Forall (App (App (Const "OnLine", Bvar 6), Bvar 1),
                    Forall (App (App (Const "OnLine", Bvar 6), Bvar 2),
                      Forall (App (App (Const "OnLine", Bvar 6), Bvar 3),
                        Forall (App (App (Const "OnLine", Bvar 9), Bvar 3),
                          Forall (App (App (Const "OnLine", Bvar 7), Bvar 4),
                            Forall (App (App (Const "OnLine", Bvar 7), Bvar 5),
                              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 11), Bvar 12),
                                Const "False"
                              ),
                                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 11), Bvar 13),
                                  Const "False"
                                ),
                                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 11), Bvar 14),
                                    Const "False"
                                  ),
                                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 11), Bvar 15),
                                      Const "False"
                                    ),
                                      Forall (Forall (App (App (App (Const "Between", Bvar 15), Bvar 16), Bvar 14),
                                        Const "False"
                                      ),
                                        Forall (Forall (App (App (App (Const "Between", Bvar 14), Bvar 17), Bvar 13),
                                          Const "False"
                                        ),
                                          App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 17), Bvar 18), Bvar 15)), App (App (App (Const "Angle", Bvar 16), Bvar 18), Bvar 14))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Line",
                Forall (Const "Line",
                  Forall (Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 7), Bvar 2),
                      Forall (App (App (Const "OnLine", Bvar 7), Bvar 3),
                        Forall (App (App (Const "OnLine", Bvar 8), Bvar 3),
                          Forall (App (App (Const "OnLine", Bvar 8), Bvar 4),
                            Forall (App (App (Const "OnLine", Bvar 9), Bvar 4),
                              Forall (App (App (Const "OnLine", Bvar 9), Bvar 5),
                                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 12), Bvar 11),
                                  Const "False"
                                ),
                                  Forall (App (App (App (Const "SameSide", Bvar 14), Bvar 11), Bvar 8),
                                    Forall (App (App (Const "Lt", App (App (Const "Add", App (App (App (Const "Angle", Bvar 15), Bvar 14), Bvar 13)), App (App (App (Const "Angle", Bvar 14), Bvar 13), Bvar 12))), App (App (Const "Add", Const "RightAngle"), Const "RightAngle")),
                                      App (App (Const "LinesInter", Bvar 11), Bvar 9)
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

  (* lines_inter_point_on_same_side_if_angle_sum_lt_180: (a : Point) -> (b : Point) -> (c : Point) -> (d : Point) -> 
  (e : Point) -> (L : Line) -> (M : Line) -> (N : Line) ->
    (OnLine a L) -> (OnLine b L) ->
    (OnLine b M) ->(OnLine c M) ->
    (OnLine c N) -> (OnLine d N) ->
    (Not (Eq Point b c)) ->
    (SameSide a d M) ->
    (Lt (Add (Angle a b c) (Angle b c d)) (Add RightAngle RightAngle)) ->   
    (OnLine e L) -> (OnLine e N) ->
    (SameSide e a M) *)
  show_kterm "lines_inter_point_on_same_side_if_angle_sum_lt_180";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Line",
                Forall (Const "Line",
                  Forall (Const "Line",
                    Forall (App (App (Const "OnLine", Bvar 7), Bvar 2),
                      Forall (App (App (Const "OnLine", Bvar 7), Bvar 3),
                        Forall (App (App (Const "OnLine", Bvar 8), Bvar 3),
                          Forall (App (App (Const "OnLine", Bvar 8), Bvar 4),
                            Forall (App (App (Const "OnLine", Bvar 9), Bvar 4),
                              Forall (App (App (Const "OnLine", Bvar 9), Bvar 5),
                                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 12), Bvar 11),
                                  Const "False"
                                ),
                                  Forall (App (App (App (Const "SameSide", Bvar 14), Bvar 11), Bvar 8),
                                    Forall (App (App (Const "Lt", App (App (Const "Add", App (App (App (Const "Angle", Bvar 15), Bvar 14), Bvar 13)), App (App (App (Const "Angle", Bvar 14), Bvar 13), Bvar 12))), App (App (Const "Add", Const "RightAngle"), Const "RightAngle")),
                                      Forall (App (App (Const "OnLine", Bvar 12), Bvar 11),
                                        Forall (App (App (Const "OnLine", Bvar 13), Bvar 10),
                                          App (App (App (Const "SameSide", Bvar 14), Bvar 18), Bvar 12)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (Const "OnLine", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnLine", Bvar 3), Bvar 1),
                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                  Const "False"
                ),
                  Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 6), Bvar 5), Bvar 4)), Const "Zero"),
                    App (App (Const "OnLine", Bvar 5), Bvar 4)
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Line",
            Forall (App (App (Const "OnLine", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnLine", Bvar 3), Bvar 1),
                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                  Const "False"
                ),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 3),
                    App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 7), Bvar 6), Bvar 5)), Const "Zero")
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 0),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 6),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 6),
                        Const "False"
                      ),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 7),
                          Const "False"
                        ),
                          Forall (Forall (App (App (Const "OnLine", Bvar 7), Bvar 6),
                            Const "False"
                          ),
                            Forall (App (App (App (Const "Between", Bvar 11), Bvar 9), Bvar 10),
                              App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (App (Const "Area", Bvar 12), Bvar 10), Bvar 9)), App (App (App (Const "Area", Bvar 9), Bvar 10), Bvar 11))), App (App (App (Const "Area", Bvar 12), Bvar 9), Bvar 11))
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
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Line",
              Forall (App (App (Const "OnLine", Bvar 4), Bvar 0),
                Forall (App (App (Const "OnLine", Bvar 4), Bvar 1),
                  Forall (App (App (Const "OnLine", Bvar 4), Bvar 2),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 6),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 6),
                        Const "False"
                      ),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 9), Bvar 7),
                          Const "False"
                        ),
                          Forall (Forall (App (App (Const "OnLine", Bvar 7), Bvar 6),
                            Const "False"
                          ),
                            Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Add", App (App (App (Const "Area", Bvar 11), Bvar 9), Bvar 8)), App (App (App (Const "Area", Bvar 8), Bvar 9), Bvar 10))), App (App (App (Const "Area", Bvar 11), Bvar 8), Bvar 10)),
                              App (App (App (Const "Between", Bvar 12), Bvar 10), Bvar 11)
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

  (* sss_congruence: (a : Point) -> (b : Point) -> (c : Point) -> (a' : Point) -> (b' : Point) -> (c' : Point) ->
  (Not (Eq Point a b)) -> (Not (Eq Point b c)) -> (Not (Eq Point a c)) ->
  (Not (Eq Point a' b')) -> (Not (Eq Point b' c')) -> (Not (Eq Point a' c')) ->
  (Eq Measure (Length a b) (Length a' b')) -> (Eq Measure (Length b c) (Length b' c')) -> 
  (Eq Measure (Length c a) (Length c' a')) ->
  (And 
  (Eq Measure (Area a b c) (Area a' b' c'))
  (And (Eq Measure (Angle a b c) (Angle a' b' c')) (And (Eq Measure (Angle b c a) (Angle b' c' a'))
  (Eq Measure (Angle c a b) (Angle c' a' b'))))) *)
  show_kterm "sss_congruence";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Point",
                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                  Const "False"
                ),
                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                    Const "False"
                  ),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 5),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                        Const "False"
                      ),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                          Const "False"
                        ),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 5),
                            Const "False"
                          ),
                            Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 11), Bvar 10)), App (App (Const "Length", Bvar 8), Bvar 7)),
                              Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 11), Bvar 10)), App (App (Const "Length", Bvar 8), Bvar 7)),
                                Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 11), Bvar 13)), App (App (Const "Length", Bvar 8), Bvar 10)),
                                  App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 14), Bvar 13), Bvar 12)), App (App (App (Const "Area", Bvar 11), Bvar 10), Bvar 9))), App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 14), Bvar 13), Bvar 12)), App (App (App (Const "Angle", Bvar 11), Bvar 10), Bvar 9))), App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 13), Bvar 12), Bvar 14)), App (App (App (Const "Angle", Bvar 10), Bvar 9), Bvar 11))), App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 12), Bvar 14), Bvar 13)), App (App (App (Const "Angle", Bvar 9), Bvar 11), Bvar 10)))))
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

  (* sas_congruence: (a : Point) -> (b : Point) -> (c : Point) -> (a' : Point) -> (b' : Point) -> (c' : Point) ->
  (Not (Eq Point a b)) -> (Not (Eq Point b c)) -> (Not (Eq Point a c)) ->
  (Not (Eq Point a' b')) -> (Not (Eq Point b' c')) -> (Not (Eq Point a' c')) ->
  (Eq Measure (Length a b) (Length a' b')) ->
  (Eq Measure (Length b c) (Length b' c')) ->
  (Eq Measure (Angle a b c) (Angle a' b' c')) ->
  (And
  (Eq Measure (Area a b c) (Area a' b' c'))
  (And (Eq Measure (Length a c) (Length a' c')) (And (Eq Measure (Angle b c a) (Angle b' c' a'))
  (Eq Measure (Angle c a b) (Angle c' a' b'))))) *)
  show_kterm "sas_congruence";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Point",
            Forall (Const "Point",
              Forall (Const "Point",
                Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                  Const "False"
                ),
                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                    Const "False"
                  ),
                    Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 5),
                      Const "False"
                    ),
                      Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                        Const "False"
                      ),
                        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 5), Bvar 4),
                          Const "False"
                        ),
                          Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 7), Bvar 5),
                            Const "False"
                          ),
                            Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 11), Bvar 10)), App (App (Const "Length", Bvar 8), Bvar 7)),
                              Forall (App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 11), Bvar 10)), App (App (Const "Length", Bvar 8), Bvar 7)),
                                Forall (App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 13), Bvar 12), Bvar 11)), App (App (App (Const "Angle", Bvar 10), Bvar 9), Bvar 8)),
                                  App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Area", Bvar 14), Bvar 13), Bvar 12)), App (App (App (Const "Area", Bvar 11), Bvar 10), Bvar 9))), App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (Const "Length", Bvar 14), Bvar 12)), App (App (Const "Length", Bvar 11), Bvar 9))), App (App (Const "And", App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 13), Bvar 12), Bvar 14)), App (App (App (Const "Angle", Bvar 10), Bvar 9), Bvar 11))), App (App (App (Const "Eq", Const "Measure"), App (App (App (Const "Angle", Bvar 12), Bvar 14), Bvar 13)), App (App (App (Const "Angle", Bvar 9), Bvar 11), Bvar 10)))))
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

  (* double_negation: (A: Prop) -> ((Not A) -> False) -> A *)
  show_kterm "double_negation";
  [%expect
    {|
    Forall (Sort 0,
      Forall (Forall (Forall (Bvar 0,
        Const "False"
      ),
        Const "False"
      ),
        Bvar 1
      )
    )
    |}];

  (* Check kenv is empty at the end *)
  if Hashtbl.length kenv <> 0 then (
    Seq.iter print_endline (Hashtbl.to_seq_keys kenv);
    [%expect.unreachable])
