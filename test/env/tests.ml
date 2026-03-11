let rec conv_to_kterm (tm : Elab.Term.term) : Kernel.Term.term =
  let open Elab.Term in
  let module KTerm = Kernel.Term in
  match tm.inner with
  | Name x -> KTerm.Const x
  | Hole _ -> failwith "hole in conv_to_kterm input"
  | Fun (_, ty, body) -> KTerm.Lam (conv_to_kterm ty, conv_to_kterm body)
  | Arrow (_, ty, ret) -> KTerm.Forall (conv_to_kterm ty, conv_to_kterm ret)
  | App (f, arg) -> KTerm.App (conv_to_kterm f, conv_to_kterm arg)
  | Sort n -> KTerm.Sort n
  | Bvar n -> KTerm.Bvar n
  | Fvar _ -> failwith "fvar in conv_to_kterm input"

let term_to_repr (term : Elab.Term.term) =
  let open Elab.Term in
  let rec term_to_repr_helper (term : term) (indent : int) (bvars : string list) =
    let indent_str = String.make (indent * 2) ' ' in
    match term.inner with
    | Name s -> Printf.sprintf "Const \"%s\"" s
    | Bvar n -> 
      Printf.sprintf "Bvar %d %s" n (List.nth bvars n)
    | Fvar _ -> failwith "fvar in term_to_repr input"
    | Fun (name, ty, body) ->
        Printf.sprintf
          "Lam (%s%s,\n%s  %s\n%s)"
          (match name with Some n -> n ^ " : "| None -> "")
          (term_to_repr_helper ty indent bvars)
          indent_str
          (term_to_repr_helper body (indent + 1) (Option.value name ~default:"" :: bvars))
          indent_str
    | Arrow (name, ty, ret) ->
        Printf.sprintf
          "Forall (%s%s,\n%s  %s\n%s)"
          (match name with Some n -> n ^ " : "| None -> "")
          (term_to_repr_helper ty indent bvars)
          indent_str
          (term_to_repr_helper ret (indent + 1) (Option.value name ~default:"" :: bvars))
          indent_str
    | App (f, arg) ->
        Printf.sprintf
          "App (%s, %s)"
          (term_to_repr_helper f indent bvars)
          (term_to_repr_helper arg indent bvars)
    | Sort n -> Printf.sprintf "Sort %d" n
    | Hole _ -> failwith "hole in term_to_repr input"
  in
  term_to_repr_helper term 0 []

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
  let ctx = Elab.Interface.create_with_env_path "../../../../../../env/env.txt" in
  let kenv = Hashtbl.copy ctx.kenv in

  let show_kterm name =
    let term = (Hashtbl.find ctx.env name).ty in
    let kterm = Hashtbl.find kenv name in
    if not (conv_to_kterm term = kterm) then
      failwith
        (Printf.sprintf "Term for %s does not match kernel term representation" name);
    let repr = term_to_repr term in
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
    Forall (C : Sort 1,
      Forall (Const "Empty",
        Bvar 1 C
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
    Forall (P : Sort 0,
      Forall (Const "False",
        Bvar 1 P
      )
    )
    |}];

  (* Exists : (A: Type) -> (A -> Prop) -> Prop *)
  show_kterm "Exists";
  [%expect
    {|
    Forall (A : Sort 1,
      Forall (Forall (Bvar 0 A,
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
    Forall (A : Sort 1,
      Forall (p : Forall (Bvar 0 A,
        Sort 0
      ),
        Forall (a : Bvar 1 A,
          Forall (h : App (Bvar 1 p, Bvar 0 a),
            App (App (Const "Exists", Bvar 3 A), Bvar 2 p)
          )
        )
      )
    )
    |}];

  (* Exists.elim : (A: Type) -> (p: A -> Prop) -> (b: Prop) -> *)
  show_kterm "Exists.elim";
  [%expect
    {|
    Forall (A : Sort 1,
      Forall (p : Forall (Bvar 0 A,
        Sort 0
      ),
        Forall (b : Sort 0,
          Forall (e : App (App (Const "Exists", Bvar 2 A), Bvar 1 p),
            Forall (Forall (a : Bvar 3 A,
              Forall (App (Bvar 3 p, Bvar 0 a),
                Bvar 3 b
              )
            ),
              Bvar 2 b
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
    Forall (A : Sort 1,
      Forall (Forall (Bvar 0 A,
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
    Forall (A : Sort 1,
      Forall (p : Forall (Bvar 0 A,
        Sort 0
      ),
        Forall (Forall (a : Bvar 1 A,
          App (Bvar 1 p, Bvar 0 a)
        ),
          App (App (Const "Forall", Bvar 2 A), Bvar 1 p)
        )
      )
    )
    |}];

  (* Forall.elim : (A: Type) -> (p: A -> Prop) ->
		Forall A p -> (a: A) -> p a *)
  show_kterm "Forall.elim";
  [%expect
    {|
    Forall (A : Sort 1,
      Forall (p : Forall (Bvar 0 A,
        Sort 0
      ),
        Forall (App (App (Const "Forall", Bvar 1 A), Bvar 0 p),
          Forall (a : Bvar 2 A,
            App (Bvar 2 p, Bvar 0 a)
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
    Forall (A : Sort 0,
      Forall (B : Sort 0,
        Forall (a : Bvar 1 A,
          Forall (b : Bvar 1 B,
            App (App (Const "And", Bvar 3 A), Bvar 2 B)
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
    Forall (A : Sort 0,
      Forall (B : Sort 0,
        Forall (C : Sort 0,
          Forall (f : Forall (Bvar 2 A,
            Forall (Bvar 2 B,
              Bvar 2 C
            )
          ),
            Forall (App (App (Const "And", Bvar 3 A), Bvar 2 B),
              Bvar 2 C
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
    Forall (A : Sort 0,
      Forall (B : Sort 0,
        Forall (Bvar 1 A,
          App (App (Const "Or", Bvar 2 A), Bvar 1 B)
        )
      )
    )
    |}];

  (* Or.inr : (A : Prop) -> (B : Prop) -> B -> Or A B *)
  show_kterm "Or.inr";
  [%expect
    {|
    Forall (A : Sort 0,
      Forall (B : Sort 0,
        Forall (Bvar 0 B,
          App (App (Const "Or", Bvar 2 A), Bvar 1 B)
        )
      )
    )
    |}];

  (* Or.elim : (A : Prop) -> (B : Prop) -> (C : Prop) ->
		Or A B -> (A -> C) -> (B -> C) -> C *)
  show_kterm "Or.elim";
  [%expect
    {|
    Forall (A : Sort 0,
      Forall (B : Sort 0,
        Forall (C : Sort 0,
          Forall (App (App (Const "Or", Bvar 2 A), Bvar 1 B),
            Forall (Forall (Bvar 3 A,
              Bvar 2 C
            ),
              Forall (Forall (Bvar 3 B,
                Bvar 3 C
              ),
                Bvar 3 C
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
    Forall (T : Sort 1,
      Forall (Bvar 0 T,
        Forall (Bvar 1 T,
          Sort 0
        )
      )
    )
    |}];

  (* Eq.intro : (T: Type) -> (t: T) -> Eq T t t *)
  show_kterm "Eq.intro";
  [%expect
    {|
    Forall (T : Sort 1,
      Forall (t : Bvar 0 T,
        App (App (App (Const "Eq", Bvar 1 T), Bvar 0 t), Bvar 0 t)
      )
    )
    |}];

  (* Eq.elim : (T: Type) -> (t: T) -> (motive : T -> Prop) -> (rfl: motive t) -> (t1: T) -> Eq T t t1 -> motive t1 *)
  show_kterm "Eq.elim";
  [%expect
    {|
    Forall (T : Sort 1,
      Forall (t : Bvar 0 T,
        Forall (motive : Forall (Bvar 1 T,
          Sort 0
        ),
          Forall (rfl : App (Bvar 0 motive, Bvar 1 t),
            Forall (t1 : Bvar 3 T,
              Forall (App (App (App (Const "Eq", Bvar 4 T), Bvar 3 t), Bvar 0 t1),
                App (Bvar 3 motive, Bvar 1 t1)
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
    Forall (a : Const "Len",
      Forall (b : Const "Len",
        Forall (c : Const "Len",
          Forall (App (App (Const "Lt", Bvar 2 a), Bvar 1 b),
            Forall (App (App (Const "Lt", Bvar 2 b), Bvar 1 c),
              App (App (Const "Lt", Bvar 4 a), Bvar 2 c)
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
    Forall (a : Const "Len",
      Forall (b : Const "Len",
        App (App (Const "Or", App (App (Const "Lt", Bvar 1 a), Bvar 0 b)), App (App (Const "Or", App (App (Const "Lt", Bvar 0 b), Bvar 1 a)), App (App (App (Const "Eq", App (App (Lam (Const "Len",
          Lam (Const "Len",
            Const "Len"
          )
        ), Bvar 1 a), Bvar 0 b)), Bvar 1 a), Bvar 0 b)))
      )
    )
    |}];

  (* LtAntisymm : (a: Len) -> (b: Len) -> Lt a b -> Lt b a -> False *)
  show_kterm "LtAntisymm";
  [%expect
    {|
    Forall (a : Const "Len",
      Forall (b : Const "Len",
        Forall (App (App (Const "Lt", Bvar 1 a), Bvar 0 b),
          Forall (App (App (Const "Lt", Bvar 1 b), Bvar 2 a),
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
    Forall (a : Const "Len",
      App (App (Const "Or", App (App (Const "Lt", Const "Zero"), Bvar 0 a)), App (App (App (Const "Eq", App (Lam (Const "Len",
        Const "Len"
      ), Bvar 0 a)), Const "Zero"), Bvar 0 a))
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
    Forall (a : Const "Len",
      Forall (b : Const "Len",
        App (App (App (Const "Eq", App (App (Lam (Const "Len",
          Lam (Const "Len",
            Const "Len"
          )
        ), Bvar 1 a), Bvar 0 b)), App (App (Const "Add", Bvar 1 a), Bvar 0 b)), App (App (Const "Add", Bvar 0 b), Bvar 1 a))
      )
    )
    |}];

  (* AddAssoc : (a: Len) -> (b: Len) -> (c: Len) -> Eq _ (Add (Add a b) c) (Add a (Add b c)) *)
  show_kterm "AddAssoc";
  [%expect
    {|
    Forall (a : Const "Len",
      Forall (b : Const "Len",
        Forall (c : Const "Len",
          App (App (App (Const "Eq", App (App (App (Lam (Const "Len",
            Lam (Const "Len",
              Lam (Const "Len",
                Const "Len"
              )
            )
          ), Bvar 2 a), Bvar 1 b), Bvar 0 c)), App (App (Const "Add", App (App (Const "Add", Bvar 2 a), Bvar 1 b)), Bvar 0 c)), App (App (Const "Add", Bvar 2 a), App (App (Const "Add", Bvar 1 b), Bvar 0 c)))
        )
      )
    )
    |}];

  (* AddZero : (a: Len) -> Eq _ (Add a Zero) a *)
  show_kterm "AddZero";
  [%expect
    {|
    Forall (a : Const "Len",
      App (App (App (Const "Eq", App (Lam (Const "Len",
        Const "Len"
      ), Bvar 0 a)), App (App (Const "Add", Bvar 0 a), Const "Zero")), Bvar 0 a)
    )
    |}];

  (* LtAdd : (a: Len) -> (b: Len) -> (c: Len) -> Lt a b -> Lt (Add a c) (Add b c) *)
  show_kterm "LtAdd";
  [%expect
    {|
    Forall (a : Const "Len",
      Forall (b : Const "Len",
        Forall (c : Const "Len",
          Forall (App (App (Const "Lt", Bvar 2 a), Bvar 1 b),
            App (App (Const "Lt", App (App (Const "Add", Bvar 3 a), Bvar 1 c)), App (App (Const "Add", Bvar 2 b), Bvar 1 c))
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
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Const "Len"
      )
    )
    |}];

  (* Angle : (a: Point) -> (b: Point) -> (c: Point) -> Len *)
  show_kterm "Angle";
  [%expect
    {|
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Forall (c : Const "Point",
          Const "Len"
        )
      )
    )
    |}];

  (* Area : (a: Point) -> (b: Point) -> (c: Point) -> Len *)
  show_kterm "Area";
  [%expect
    {|
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Forall (c : Const "Point",
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
    Forall (L : Const "Line",
      App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
        App (App (Const "OnLine", Bvar 0 a), Bvar 1 L)
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
    Forall (L : Const "Line",
      Forall (b : Const "Point",
        Forall (c : Const "Point",
          Forall (App (App (Const "OnLine", Bvar 1 b), Bvar 2 L),
            Forall (App (App (Const "OnLine", Bvar 1 c), Bvar 3 L),
              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3 b), Bvar 2 c),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
                  App (App (Const "And", App (App (Const "OnLine", Bvar 0 a), Bvar 6 L)), App (App (App (Const "Between", Bvar 5 b), Bvar 0 a), Bvar 4 c))
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
    Forall (L : Const "Line",
      Forall (b : Const "Point",
        Forall (c : Const "Point",
          Forall (App (App (Const "OnLine", Bvar 1 b), Bvar 2 L),
            Forall (App (App (Const "OnLine", Bvar 1 c), Bvar 3 L),
              Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3 b), Bvar 2 c),
                Const "False"
              ),
                App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
                  App (App (Const "And", App (App (Const "OnLine", Bvar 0 a), Bvar 6 L)), App (App (App (Const "Between", Bvar 5 b), Bvar 4 c), Bvar 0 a))
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
    Forall (L : Const "Line",
      Forall (b : Const "Point",
        Forall (Forall (App (App (Const "OnLine", Bvar 0 b), Bvar 1 L),
          Const "False"
        ),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (App (Const "SameSide", Bvar 0 a), Bvar 2 b), Bvar 3 L)
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
    Forall (L : Const "Line",
      Forall (b : Const "Point",
        Forall (Forall (App (App (Const "OnLine", Bvar 0 b), Bvar 1 L),
          Const "False"
        ),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0 a), Bvar 3 L),
              Const "False"
            )), Forall (App (App (App (Const "SameSide", Bvar 0 a), Bvar 2 b), Bvar 3 L),
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
    Forall (aa : Const "Circle",
      App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
        App (App (Const "OnCircle", Bvar 0 a), Bvar 1 aa)
      ))
    )
    |}];

  (* pt_inside_circle : (aa : Circle) ->
	 Exists Point (fun (a : Point) => InCircle a aa) *)
  show_kterm "pt_inside_circle";
  [%expect
    {|
    Forall (aa : Const "Circle",
      App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
        App (App (Const "InCircle", Bvar 0 a), Bvar 1 aa)
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
    Forall (aa : Const "Circle",
      App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
        App (App (Const "And", Forall (App (App (Const "OnCircle", Bvar 0 a), Bvar 1 aa),
          Const "False"
        )), Forall (App (App (Const "InCircle", Bvar 0 a), Bvar 1 aa),
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
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 a), Bvar 0 b),
          Const "False"
        ),
          App (App (Const "Exists", Const "Line"), Lam (L : Const "Line",
            App (App (Const "And", App (App (Const "OnLine", Bvar 3 a), Bvar 0 L)), App (App (Const "OnLine", Bvar 2 b), Bvar 0 L))
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
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 a), Bvar 0 b),
          Const "False"
        ),
          App (App (Const "Exists", Const "Circle"), Lam (aa : Const "Circle",
            App (App (Const "And", App (App (Const "CenterCircle", Bvar 3 a), Bvar 0 aa)), App (App (Const "OnCircle", Bvar 2 b), Bvar 0 aa))
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
    Forall (L : Const "Line",
      Forall (M : Const "Line",
        Forall (App (App (Const "LinesInter", Bvar 1 L), Bvar 0 M),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (Const "And", App (App (Const "OnLine", Bvar 0 a), Bvar 3 L)), App (App (Const "OnLine", Bvar 0 a), Bvar 2 M))
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
    Forall (L : Const "Line",
      Forall (aa : Const "Circle",
        Forall (App (App (Const "LineCircleInter", Bvar 1 L), Bvar 0 aa),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (Const "And", App (App (Const "OnLine", Bvar 0 a), Bvar 3 L)), App (App (Const "OnCircle", Bvar 0 a), Bvar 2 aa))
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
    Forall (L : Const "Line",
      Forall (aa : Const "Circle",
        Forall (App (App (Const "LineCircleInter", Bvar 1 L), Bvar 0 aa),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (Const "Exists", Const "Point"), Lam (b : Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 a), Bvar 0 b),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnLine", Bvar 1 a), Bvar 4 L)), App (App (Const "And", App (App (Const "OnLine", Bvar 0 b), Bvar 4 L)), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 a), Bvar 3 aa)), App (App (Const "OnCircle", Bvar 0 b), Bvar 3 aa)))))
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
    Forall (L : Const "Line",
      Forall (aa : Const "Circle",
        Forall (b : Const "Point",
          Forall (c : Const "Point",
            Forall (App (App (Const "OnLine", Bvar 1 b), Bvar 3 L),
              Forall (App (App (Const "OnLine", Bvar 1 c), Bvar 4 L),
                Forall (App (App (Const "InCircle", Bvar 3 b), Bvar 4 aa),
                  Forall (Forall (App (App (Const "OnCircle", Bvar 3 c), Bvar 5 aa),
                    Const "False"
                  ),
                    Forall (Forall (App (App (Const "InCircle", Bvar 4 c), Bvar 6 aa),
                      Const "False"
                    ),
                      App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
                        App (App (Const "And", App (App (Const "OnLine", Bvar 0 a), Bvar 9 L)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 a), Bvar 8 aa)), App (App (App (Const "Between", Bvar 7 b), Bvar 0 a), Bvar 6 c)))
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
    Forall (L : Const "Line",
      Forall (aa : Const "Circle",
        Forall (b : Const "Point",
          Forall (c : Const "Point",
            Forall (App (App (Const "OnLine", Bvar 1 b), Bvar 3 L),
              Forall (App (App (Const "OnLine", Bvar 1 c), Bvar 4 L),
                Forall (App (App (Const "InCircle", Bvar 3 b), Bvar 4 aa),
                  Forall (Forall (App (App (App (Const "Eq", Const "Point"), Bvar 3 c), Bvar 4 b),
                    Const "False"
                  ),
                    App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
                      App (App (Const "And", App (App (Const "OnLine", Bvar 0 a), Bvar 8 L)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 a), Bvar 7 aa)), App (App (App (Const "Between", Bvar 0 a), Bvar 6 b), Bvar 5 c)))
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
    Forall (aa : Const "Circle",
      Forall (bb : Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1 aa), Bvar 0 bb),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (Const "And", App (App (Const "OnCircle", Bvar 0 a), Bvar 3 aa)), App (App (Const "OnCircle", Bvar 0 a), Bvar 2 bb))
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
    Forall (aa : Const "Circle",
      Forall (bb : Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1 aa), Bvar 0 bb),
          App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
            App (App (Const "Exists", Const "Point"), Lam (b : Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", Const "Point"), Bvar 1 a), Bvar 0 b),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 a), Bvar 4 aa)), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 a), Bvar 3 bb)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 b), Bvar 4 aa)), App (App (Const "OnCircle", Bvar 0 b), Bvar 3 bb)))))
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
    Forall (b : Const "Point",
      Forall (c : Const "Point",
        Forall (d : Const "Point",
          Forall (L : Const "Line",
            Forall (aa : Const "Circle",
              Forall (bb : Const "Circle",
                Forall (App (App (Const "OnLine", Bvar 4 c), Bvar 2 L),
                  Forall (App (App (Const "OnLine", Bvar 4 d), Bvar 3 L),
                    Forall (Forall (App (App (Const "OnLine", Bvar 7 b), Bvar 4 L),
                      Const "False"
                    ),
                      Forall (App (App (Const "CenterCircle", Bvar 7 c), Bvar 4 aa),
                        Forall (App (App (Const "CenterCircle", Bvar 7 d), Bvar 4 bb),
                          Forall (App (App (Const "CirclesInter", Bvar 6 aa), Bvar 5 bb),
                            App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
                              App (App (Const "And", App (App (App (Const "SameSide", Bvar 0 a), Bvar 12 b), Bvar 9 L)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 a), Bvar 8 aa)), App (App (Const "OnCircle", Bvar 0 a), Bvar 7 bb)))
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
    Forall (b : Const "Point",
      Forall (c : Const "Point",
        Forall (d : Const "Point",
          Forall (L : Const "Line",
            Forall (aa : Const "Circle",
              Forall (bb : Const "Circle",
                Forall (App (App (Const "OnLine", Bvar 4 c), Bvar 2 L),
                  Forall (App (App (Const "OnLine", Bvar 4 d), Bvar 3 L),
                    Forall (Forall (App (App (Const "OnLine", Bvar 7 b), Bvar 4 L),
                      Const "False"
                    ),
                      Forall (App (App (Const "CenterCircle", Bvar 7 c), Bvar 4 aa),
                        Forall (App (App (Const "CenterCircle", Bvar 7 d), Bvar 4 bb),
                          Forall (App (App (Const "CirclesInter", Bvar 6 aa), Bvar 5 bb),
                            App (App (Const "Exists", Const "Point"), Lam (a : Const "Point",
                              App (App (Const "And", Forall (App (App (Const "OnLine", Bvar 0 a), Bvar 9 L),
                                Const "False"
                              )), App (App (Const "And", Forall (App (App (App (Const "SameSide", Bvar 0 a), Bvar 12 b), Bvar 9 L),
                                Const "False"
                              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 a), Bvar 8 aa)), App (App (Const "OnCircle", Bvar 0 a), Bvar 7 bb))))
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
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Forall (aa : Const "Circle",
          Forall (bb : Const "Circle",
            Forall (App (App (Const "OnCircle", Bvar 2 b), Bvar 1 aa),
              Forall (App (App (Const "OnCircle", Bvar 4 a), Bvar 1 bb),
                Forall (App (App (Const "InCircle", Bvar 5 a), Bvar 3 aa),
                  Forall (App (App (Const "InCircle", Bvar 5 b), Bvar 3 bb),
                    App (App (Const "CirclesInter", Bvar 5 aa), Bvar 4 bb)
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
    Forall (a : Const "Point",
      Forall (aa : Const "Circle",
        Forall (App (App (Const "CenterCircle", Bvar 1 a), Bvar 0 aa),
          App (App (Const "InCircle", Bvar 2 a), Bvar 1 aa)
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
    Forall (a : Const "Circle",
      Forall (b : Const "Circle",
        Forall (App (App (Const "CirclesInter", Bvar 1 a), Bvar 0 b),
          App (App (Const "Exists", Const "Point"), Lam (c : Const "Point",
            App (App (Const "Exists", Const "Point"), Lam (d : Const "Point",
              App (App (Const "And", Forall (App (App (App (Const "Eq", App (App (App (App (App (Lam (Const "Circle",
                Lam (Const "Circle",
                  Lam (App (App (Const "CirclesInter", Bvar 1 ), Bvar 0 ),
                    Lam (Const "Point",
                      Lam (Const "Point",
                        Const "Point"
                      )
                    )
                  )
                )
              ), Bvar 4 a), Bvar 3 b), Bvar 2 ), Bvar 1 c), Bvar 0 d)), Bvar 1 c), Bvar 0 d),
                Const "False"
              )), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 c), Bvar 4 a)), App (App (Const "And", App (App (Const "OnCircle", Bvar 1 c), Bvar 3 b)), App (App (Const "And", App (App (Const "OnCircle", Bvar 0 d), Bvar 4 a)), App (App (Const "OnCircle", Bvar 0 d), Bvar 3 b)))))
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
    Forall (a : Const "Point",
      Forall (b : Const "Point",
        Forall (c : Const "Point",
          Forall (d : Const "Circle",
            Forall (App (App (Const "CenterCircle", Bvar 3 a), Bvar 0 d),
              Forall (App (App (Const "OnCircle", Bvar 3 b), Bvar 1 d),
                App (App (Const "And", Forall (App (App (App (Const "Eq", App (App (App (App (App (App (Lam (Const "Point",
                  Lam (Const "Point",
                    Lam (Const "Point",
                      Lam (Const "Circle",
                        Lam (App (App (Const "CenterCircle", Bvar 3 ), Bvar 0 ),
                          Lam (App (App (Const "OnCircle", Bvar 3 ), Bvar 1 ),
                            Const "Len"
                          )
                        )
                      )
                    )
                  )
                ), Bvar 5 a), Bvar 4 b), Bvar 3 c), Bvar 2 d), Bvar 1 ), Bvar 0 )), App (App (Const "Length", Bvar 5 a), Bvar 4 b)), App (App (Const "Length", Bvar 5 a), Bvar 3 c)),
                  App (App (Const "OnCircle", Bvar 4 c), Bvar 3 d)
                )), Forall (App (App (Const "OnCircle", Bvar 3 c), Bvar 2 d),
                  App (App (App (Const "Eq", App (App (App (App (App (App (App (Lam (Const "Point",
                    Lam (Const "Point",
                      Lam (Const "Point",
                        Lam (Const "Circle",
                          Lam (App (App (Const "CenterCircle", Bvar 3 ), Bvar 0 ),
                            Lam (App (App (Const "OnCircle", Bvar 3 ), Bvar 1 ),
                              Lam (App (App (Const "OnCircle", Bvar 3 ), Bvar 2 ),
                                Const "Len"
                              )
                            )
                          )
                        )
                      )
                    )
                  ), Bvar 6 a), Bvar 5 b), Bvar 4 c), Bvar 3 d), Bvar 2 ), Bvar 1 ), Bvar 0 )), App (App (Const "Length", Bvar 6 a), Bvar 5 b)), App (App (Const "Length", Bvar 6 a), Bvar 4 c))
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
