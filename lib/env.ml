open Term

(* Create an expression where func is applied to all arguments in order *)
(* Ex: f a b c -> App(App (App (f, a), b), c) *)
let application_multiple_arguments (func: term) (args: term list): term = 
  List.fold_left
    (fun application_so_far first_arg -> App (application_so_far, first_arg))
    func
    args

let type0 = Sort 0                 (* "Type" *)
let pi (a : term) (b : term) = Forall (a, b)  (* Π (_ : a), b *)
let app2 f x y = App (App (f, x), y)
let exists_ty : term =
  pi (Sort 1)
    (pi (pi (Bvar 0) type0)   (* B : A -> Prop *)
        type0)                (* Exists A B : Prop *)
let exists_intro_ty : term =
  pi (Sort 1)
    (pi (pi (Bvar 0) type0)          (* B : A -> Prop *)
      (pi (Bvar 1)                   (* a : A   (A is Bvar 1 here) *)
        (pi (App (Bvar 1, Bvar 0))   (* b : B a *)
          (app2 (Const "Exists") (Bvar 3) (Bvar 2)))))  (* Exists A B *)

let add_exists (env : environment) : unit =
  Hashtbl.replace env "Exists" exists_ty;
  Hashtbl.replace env "Exists.intro" exists_intro_ty

let mk_axioms_env () =
  let env = Hashtbl.create 16 in
  (* Built-in geometric types *)
  Hashtbl.add env "Point" (Sort 1);
  Hashtbl.add env "Line" (Sort 1);
  Hashtbl.add env "Circle" (Sort 1);
  add_exists env;
  (* Empty: Type — the empty type (no inhabitants); used for negation (¬P = P -> Empty) *)
  Hashtbl.add env "Empty" (Sort 1);
  (* Empty.elim: (C : Type) -> Empty -> C — ex falso quodlibet: from a proof of Empty, derive any C *)
  let empty_elim_type =
    (* (C : Type) *)
    Forall (Sort 1,
      (* (e : Empty) -> C *)
      Forall (Const "Empty", Bvar 1))
  in
  Hashtbl.add env "Empty.elim" empty_elim_type;

  (* And: (A : Prop) -> (B : Prop) -> Prop — conjunction of two propositions *)
  let and_type =
    Forall (Sort 0, Forall (Sort 0, Sort 0))
  in
  Hashtbl.add env "And" and_type;

  (* And.intro: (A : Prop) -> (B : Prop) -> (a : A) -> (b : B) -> And A B *)
  let and_intro_type =
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Bvar 1, (* A *)
          Forall (Bvar 1, (* B *)
            App (App (Const "And", Bvar 3), Bvar 2)))))
  in
  Hashtbl.add env "And.intro" and_intro_type;

  (* And.elim: (A : Prop) -> (B : Prop) -> (C : Type) -> (f : A -> B -> C) -> (h : And A B) -> C *)
  let and_elim_type =
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Sort 0,
          Forall (Forall (Bvar 4, Forall (Bvar 3, Bvar 2)),
            Forall (App (App (Const "And", Bvar 4), Bvar 3), Bvar 2)))))
  in
  Hashtbl.add env "And.elim" and_elim_type;

  (* Exists.elim from main branch:
     (A : Type) -> (p : A -> Prop) -> (b : Prop) ->
     (e : Exists A p) ->
     (h : Forall (a : A), p a -> b) ->
     b
  *)
  Hashtbl.add env "Exists.elim"
    (Forall (Sort 1,                         (* A : Type *)
      Forall (Forall (Bvar 0, Sort 0),       (* p : A -> Prop *)
        Forall (Sort 0,                      (* b : Prop *)
          Forall (App (App (Const "Exists", Bvar 2), Bvar 1),  (* e : Exists A p *)
            Forall (
              Forall (Bvar 3,                (* a : A *)
                Forall (App (Bvar 4, Bvar 0), (* p a *)
                  Bvar 3)),                  (* b *)
              Bvar 2))))));                  (* result: b *)

  Hashtbl.add env "Eq" (
    Forall (Sort 1,
      (Forall (Bvar 0, Forall (Bvar 1, Sort 0)))
    )
  );
  Hashtbl.add env "Eq.intro" (
    Forall (Sort 1, 
      Forall (Bvar 0,
        application_multiple_arguments (Const "Eq") [Bvar 1; Bvar 0; Bvar 0]
      )
    )
  );

  Hashtbl.add env "Eq.elim" (
    Forall (Sort 1, (* A: Type *)
    Forall (Bvar 0, (* a: A *)
    Forall (Forall (Bvar 1, Sort 0), (* motive: A -> Prop *)
    Forall (App (Bvar 0, Bvar 1), (* refl: motive a *)
    Forall (Bvar 3, (* b: A *)
    Forall (
      (* eq: Eq A a b *)
      application_multiple_arguments (Const "Eq") [Bvar 4; Bvar 3; Bvar 0], 
      (* motive b *)
      App (Bvar 3, Bvar 1)
    ))))))
  );
  
  (* Length (magnitude) axioms *)
  Hashtbl.add env "Len" (Sort 1);
  (* There exists a total order "Lt" on Len *)
  Hashtbl.add env "Lt" (Forall (Const "Len", Forall (Const "Len", Sort 0)));
  Hashtbl.add env "LtTrans" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    Forall (Const "Len", (* c : Len -> *)
    Forall (App (App (Const "Lt", Bvar 2), Bvar 1), (* Lt a b -> *)
    Forall (App (App (Const "Lt", Bvar 2), Bvar 1), (* Lt b c -> *)
    (App (App (Const "Lt", Bvar 4), Bvar 2)) (*Lt a c *)
  ))))));
  Hashtbl.add env "LtTricot" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    (App (App (Const "Or", (*Lt a b \/ *)
      App (App (Const "Lt", Bvar 1), Bvar 0)),
      (App (App (Const "Or", (* Lt b a \/ Eq Len a b *)
        App (App (Const "Lt", Bvar 0), Bvar 1)),
        App (App (App (Const "Eq", Const "Len"), Bvar 1), Bvar 0)
      ))
    ))
  )));
  (* There exists an element zero of len that is the least of sort len *)
  Hashtbl.add env "Zero" (Const "Len");
  Hashtbl.add env "ZeroLeast" (
    Forall (Const "Len", (* a : Len -> *)
    App (App (Const "Or", (*Lt Zero a \/ Eq Len Zero a *)
      App (App (Const "Lt", Const "Zero"), Bvar 0)),
      App (App (App (Const "Eq", Const "Len"), Const "Zero"), Bvar 0))
    )
  );
  (* There is an operation Add on Len which is commutative and associative *)
  Hashtbl.add env "Add" (Forall (Const "Len", Forall (Const "Len", Const "Len")));
  Hashtbl.add env "AddComm" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    (App (App (App (Const "Eq", Const "Len"), (* Add a b = Add b a *)
      App (App (Const "Add", Bvar 1), Bvar 0)),
      App (App (Const "Add", Bvar 0), Bvar 1)
    ))
  )));
  Hashtbl.add env "AddAssoc" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    Forall (Const "Len", (* c : Len -> *)
    (App (App (App (Const "Eq", Const "Len"), (* Add (Add a b) c = Add a (Add b c) *)
      App (App (Const "Add",
        App (App (Const "Add", Bvar 2), Bvar 1)), (* Add a b *)
        Bvar 0 (* c *)
      )),
      App (App (Const "Add",
        Bvar 2), (* a *)
        App (App (Const "Add", Bvar 1), Bvar 0) (* Add b c *)
      )
    ))
  ))));
  Hashtbl.add env "AddZero" (
    Forall (Const "Len", (* a : Len -> *)
    (App (App (App (Const "Eq", Const "Len"), (* Eq Len (Add Zero a) a*)
      App (App (Const "Add", Const "Zero"), Bvar 0)),
      Bvar 0
    )) 
  ));
  Hashtbl.add env "LtAdd" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    Forall (Const "Len", (* c : Len -> *)
    Forall (App (App (Const "Lt", Bvar 2), Bvar 1), (* Lt a b -> *)
    (App (App (Const "Lt", (* Lt (Add a c) (Add b c) *)
      App (App (Const "Add", Bvar 3), Bvar 1)), (* note that we increment the indices *)
      App (App (Const "Add", Bvar 2), Bvar 1)
    ))
  )))));
  Hashtbl.add env "Length" (Forall (Const "Point", Forall (Const "Point", Const "Len")));

  env