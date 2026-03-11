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

  (* Exists.elim : (A: Type) -> (p: A -> Prop) -> (b: Prop) -> *)
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

  (* Point : Type *)
  show_kterm "Point";
  [%expect {| Sort 1 |}];

  (* Line : Type *)
  show_kterm "Line";
  [%expect {| Sort 1 |}];

  (* Circle : Type *)
  show_kterm "Circle";
  [%expect {| Sort 1 |}];

  (* Len : Type *)
  show_kterm "Len";
  [%expect {| Sort 1 |}];

  (* Lt : Len -> Len -> Prop *)
  show_kterm "Lt";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        Sort 0
      )
    )
    |}];

  (* LtTrans : (a: Len) -> (b: Len) -> (c: Len) -> Lt a b -> Lt b c -> Lt a c *)
  show_kterm "LtTrans";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        Forall (Const "Len",
          Forall (App (App (Const "Lt", Bvar 2), Bvar 1),
            Forall (App (App (Const "Lt", Bvar 2), Bvar 1),
              App (App (Const "Lt", Bvar 4), Bvar 2)
            )
          )
        )
      )
    )
    |}];

  (* LtTricot : (a: Len) -> (b: Len) -> Or (Lt a b) (Or (Lt b a) (Eq _ a b)) *)
  show_kterm "LtTricot";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        App (App (Const "Or", App (App (Const "Lt", Bvar 1), Bvar 0)), App (App (Const "Or", App (App (Const "Lt", Bvar 0), Bvar 1)), App (App (App (Const "Eq", App (App (Lam (Const "Len",
          Lam (Const "Len",
            Const "Len"
          )
        ), Bvar 1), Bvar 0)), Bvar 1), Bvar 0)))
      )
    )
    |}];

  (* LtAntisymm : (a: Len) -> (b: Len) -> Lt a b -> Lt b a -> False *)
  show_kterm "LtAntisymm";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        Forall (App (App (Const "Lt", Bvar 1), Bvar 0),
          Forall (App (App (Const "Lt", Bvar 1), Bvar 2),
            Const "False"
          )
        )
      )
    )
    |}];

  (* Zero : Len *)
  show_kterm "Zero";
  [%expect {| Const "Len" |}];

  (* ZeroLeast : (a: Len) -> Or (Lt Zero a) (Eq _ Zero a) *)
  show_kterm "ZeroLeast";
  [%expect
    {|
    Forall (Const "Len",
      App (App (Const "Or", App (App (Const "Lt", Const "Zero"), Bvar 0)), App (App (App (Const "Eq", App (Lam (Const "Len",
        Const "Len"
      ), Bvar 0)), Const "Zero"), Bvar 0))
    )
    |}];

  (* Add : Len -> Len -> Len *)
  show_kterm "Add";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        Const "Len"
      )
    )
    |}];

  (* AddComm : (a: Len) -> (b: Len) -> Eq _ (Add a b) (Add b a) *)
  show_kterm "AddComm";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        App (App (App (Const "Eq", App (App (Lam (Const "Len",
          Lam (Const "Len",
            Const "Len"
          )
        ), Bvar 1), Bvar 0)), App (App (Const "Add", Bvar 1), Bvar 0)), App (App (Const "Add", Bvar 0), Bvar 1))
      )
    )
    |}];

  (* AddAssoc : (a: Len) -> (b: Len) -> (c: Len) -> Eq _ (Add (Add a b) c) (Add a (Add b c)) *)
  show_kterm "AddAssoc";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        Forall (Const "Len",
          App (App (App (Const "Eq", App (App (App (Lam (Const "Len",
            Lam (Const "Len",
              Lam (Const "Len",
                Const "Len"
              )
            )
          ), Bvar 2), Bvar 1), Bvar 0)), App (App (Const "Add", App (App (Const "Add", Bvar 2), Bvar 1)), Bvar 0)), App (App (Const "Add", Bvar 2), App (App (Const "Add", Bvar 1), Bvar 0)))
        )
      )
    )
    |}];

  (* AddZero : (a: Len) -> Eq _ (Add a Zero) a *)
  show_kterm "AddZero";
  [%expect
    {|
    Forall (Const "Len",
      App (App (App (Const "Eq", App (Lam (Const "Len",
        Const "Len"
      ), Bvar 0)), App (App (Const "Add", Bvar 0), Const "Zero")), Bvar 0)
    )
    |}];

  (* LtAdd : (a: Len) -> (b: Len) -> (c: Len) -> Lt a b -> Lt (Add a c) (Add b c) *)
  show_kterm "LtAdd";
  [%expect
    {|
    Forall (Const "Len",
      Forall (Const "Len",
        Forall (Const "Len",
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

  (* Length : (a: Point) -> (b: Point) -> Len *)
  show_kterm "Length";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Const "Len"
      )
    )
    |}];

  (* Angle : (a: Point) -> (b: Point) -> (c: Point) -> Len *)
  show_kterm "Angle";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Const "Len"
        )
      )
    )
    |}];

  (* Area : (a: Point) -> (b: Point) -> (c: Point) -> Len *)
  show_kterm "Area";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Const "Len"
        )
      )
    )
    |}];

  (* RightAngle : Len *)
  show_kterm "RightAngle";
  [%expect {| Const "Len" |}];

  (* pt_on_line : (L : Line) ->
	 Exists Point (fun (a : Point) => OnLine a L) *)
  show_kterm "pt_on_line";
  [%expect
    {|
    Forall (Const "Line",
      App (App (Const "Exists", Const "Point"), Lam (Const "Point",
        App (App (Const "OnLine", Bvar 0), Bvar 1)
      ))
    )
    |}];

  (* pt_between_on_line : (L : Line) -> (b : Point) -> (c : Point) ->
	 OnLine b L -> OnLine c L -> (Eq Point b c -> False) ->
	 Exists Point (fun (a : Point) =>
		And (OnLine a L) (Between b a c)) *)
  show_kterm "pt_between_on_line";
  [%expect
    {|
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (App (Const "OnLine", Bvar 1), Bvar 2),
            Forall (App (App (Const "OnLine", Bvar 1), Bvar 3),
              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 2),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                  App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 6)), App (App (App (Const "Between", Bvar 5), Bvar 0), Bvar 4))
                ))
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_extension_on_line : (L : Line) -> (b : Point) -> (c : Point) ->
	 OnLine b L -> OnLine c L -> (Eq Point b c -> False) ->
	 Exists Point (fun (a : Point) =>
		And (OnLine a L) (Between b c a)) *)
  show_kterm "pt_extension_on_line";
  [%expect
    {|
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (App (App (Const "OnLine", Bvar 1), Bvar 2),
            Forall (App (App (Const "OnLine", Bvar 1), Bvar 3),
              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3), Bvar 2),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam (Const "Point",
                  App (App (Const "And", App (App (Const "OnLine", Bvar 0), Bvar 6)), App (App (App (Const "Between", Bvar 5), Bvar 4), Bvar 0))
                ))
              )
            )
          )
        )
      )
    )
    |}];

  (* pt_sameside_of_not_online : (L : Line) -> (b : Point) ->
	 (OnLine b L -> False) ->
	 Exists Point (fun (a : Point) => SameSide a b L) *)
  show_kterm "pt_sameside_of_not_online";
  [%expect
    {|
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (Forall (App (App (Const "OnLine", Bvar 0), Bvar 1),
          Const "False"
        ),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (App (Const "SameSide", Bvar 0), Bvar 2), Bvar 3)
          ))
        )
      )
    )
    |}];

  (* pt_oppositeside_of_not_online : (L : Line) -> (b : Point) ->
	 (OnLine b L -> False) ->
	 Exists Point (fun (a : Point) =>
		And (OnLine a L -> False)
			 (SameSide a b L -> False)) *)
  show_kterm "pt_oppositeside_of_not_online";
  [%expect
    {|
    Forall (Const "Line",
      Forall (Const "Point",
        Forall (Forall (App (App (Const "OnLine", Bvar 0), Bvar 1),
          Const "False"
        ),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0), Bvar 3),
              Const "False"
            )), Forall (App (App (App (Const "SameSide", Bvar 0), Bvar 2), Bvar 3),
              Const "False"
            ))
          ))
        )
      )
    )
    |}];

  (* pt_on_circle : (aa : Circle) ->
	 Exists Point (fun (a : Point) => OnCircle a aa) *)
  show_kterm "pt_on_circle";
  [%expect
    {|
    Forall (Const "Circle",
      App (App (Const "Exists", Const "Point"), Lam (Const "Point",
        App (App (Const "OnCircle", Bvar 0), Bvar 1)
      ))
    )
    |}];

  (* pt_inside_circle : (aa : Circle) ->
	 Exists Point (fun (a : Point) => InCircle a aa) *)
  show_kterm "pt_inside_circle";
  [%expect
    {|
    Forall (Const "Circle",
      App (App (Const "Exists", Const "Point"), Lam (Const "Point",
        App (App (Const "InCircle", Bvar 0), Bvar 1)
      ))
    )
    |}];

  (* pt_outside_circle : (aa : Circle) ->
	 Exists Point (fun (a : Point) =>
		And (OnCircle a aa -> False)
			 (InCircle a aa -> False)) *)
  show_kterm "pt_outside_circle";
  [%expect
    {|
    Forall (Const "Circle",
      App (App (Const "Exists", Const "Point"), Lam (Const "Point",
        App (App (Const "And", Forall (App (App (Const "OnCircle", Bvar 0), Bvar 1),
          Const "False"
        )), Forall (App (App (Const "InCircle", Bvar 0), Bvar 1),
          Const "False"
        ))
      ))
    )
    |}];

  (* line_of_pts : (a : Point) -> (b : Point) -> (Eq Point a b -> False) ->
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

  (* circle_of_ne : (a : Point) -> (b : Point) -> (Eq Point a b -> False) ->
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

  (* pt_of_linesinter : (L : Line) -> (M : Line) -> LinesInter L M ->
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

  (* pt_of_linecircleinter : (L : Line) -> (aa : Circle) -> LineCircleInter L aa ->
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

  (* pts_of_linecircleinter : (L : Line) -> (aa : Circle) -> LineCircleInter L aa ->
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

  (* pt_oncircle_between_inside_outside : (L : Line) -> (aa : Circle) -> (b : Point) -> (c : Point) ->
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

  (* pt_oncircle_extension_from_inside : (L : Line) -> (aa : Circle) -> (b : Point) -> (c : Point) ->
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

  (* pt_of_circlesinter : (aa : Circle) -> (bb : Circle) -> CirclesInter aa bb ->
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

  (* pts_of_circlesinter : (aa : Circle) -> (bb : Circle) -> CirclesInter aa bb ->
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

  (* pt_sameside_of_circlesinter : (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) -> (aa : Circle) -> (bb : Circle) ->
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

  (* pt_oppositeside_of_circlesinter : (b : Point) -> (c : Point) -> (d : Point) -> (L : Line) -> (aa : Circle) -> (bb : Circle) ->
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

  (* circlesinter_of_inside_on_circle : (a: Point) -> (b: Point) -> (aa: Circle) -> (bb: Circle) ->
	  OnCircle b aa -> OnCircle a bb -> InCircle a aa -> InCircle b bb -> CirclesInter aa bb *)
  show_kterm "circlesinter_of_inside_on_circle";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Circle",
          Forall (Const "Circle",
            Forall (App (App (Const "OnCircle", Bvar 2), Bvar 1),
              Forall (App (App (Const "OnCircle", Bvar 4), Bvar 1),
                Forall (App (App (Const "InCircle", Bvar 5), Bvar 3),
                  Forall (App (App (Const "InCircle", Bvar 5), Bvar 3),
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

  (* inside_circle_of_center : (a: Point) -> (aa: Circle) -> *)
  show_kterm "inside_circle_of_center";
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

  (* PtsOfCirclesinter : (a : Circle) -> (b : Circle) -> CirclesInter a b ->
		Exists Point (fun (c : Point) =>
		Exists Point (fun (d : Point) =>
		And (Eq _ c d -> False) (
		And (OnCircle c a) (
		And (OnCircle c b) (
		And (OnCircle d a) (OnCircle d b)))))) *)
  show_kterm "PtsOfCirclesinter";
  [%expect
    {|
    Forall (Const "Circle",
      Forall (Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1), Bvar 0),
          App (App (Const "Exists", Const "Point"), Lam (Const "Point",
            App (App (Const "Exists", Const "Point"), Lam (Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", App (App (App (App (App (Lam (Const "Circle",
                Lam (Const "Circle",
                  Lam (App (App (Const "CirclesInter", Bvar 1), Bvar 0),
                    Lam (Const "Point",
                      Lam (Const "Point",
                        Const "Point"
                      )
                    )
                  )
                )
              ), Bvar 4), Bvar 3), Bvar 2), Bvar 1), Bvar 0)), Bvar 1), Bvar 0),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 1), Bvar 4)), App (App (Const "And", App (App (Const "OnCircle", Bvar 1), Bvar 3)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0), Bvar 4)), App (App (Const "OnCircle", Bvar 0), Bvar 3)))))
            ))
          ))
        )
      )
    )
    |}];

  (* OnCircleIffLengthEq : (a : Point) -> (b : Point) -> (c : Point) -> (d : Circle) ->
		CenterCircle a d -> OnCircle b d -> *)
  show_kterm "OnCircleIffLengthEq";
  [%expect
    {|
    Forall (Const "Point",
      Forall (Const "Point",
        Forall (Const "Point",
          Forall (Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
              Forall (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                App (App (Const "And", Forall (App (App (App (Const "Eq", App (App (App (App (App (App (Lam (Const "Point",
                  Lam (Const "Point",
                    Lam (Const "Point",
                      Lam (Const "Circle",
                        Lam (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
                          Lam (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                            Const "Len"
                          )
                        )
                      )
                    )
                  )
                ), Bvar 5), Bvar 4), Bvar 3), Bvar 2), Bvar 1), Bvar 0)), App (App (Const "Length", Bvar 5), Bvar 4)), App (App (Const "Length", Bvar 5), Bvar 3)),
                  App (App (Const "OnCircle", Bvar 4), Bvar 3)
                )), Forall (App (App (Const "OnCircle", Bvar 3), Bvar 2),
                  App (App (App (Const "Eq", App (App (App (App (App (App (App (Lam (Const "Point",
                    Lam (Const "Point",
                      Lam (Const "Point",
                        Lam (Const "Circle",
                          Lam (App (App (Const "CenterCircle", Bvar 3), Bvar 0),
                            Lam (App (App (Const "OnCircle", Bvar 3), Bvar 1),
                              Lam (App (App (Const "OnCircle", Bvar 3), Bvar 2),
                                Const "Len"
                              )
                            )
                          )
                        )
                      )
                    )
                  ), Bvar 6), Bvar 5), Bvar 4), Bvar 3), Bvar 2), Bvar 1), Bvar 0)), App (App (Const "Length", Bvar 6), Bvar 5)), App (App (Const "Length", Bvar 6), Bvar 4))
                ))
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
