(** decides (in)equalities on Measures using Fourier–Motzkin elimination (at least that's
    the goal) *)

(** produces a proof of type ∀ (a b : Measure), n * a < n * b → a < b where n * a denotes
    a + a + ... + a (n times) *)
let lt_cancel_mul (n : int) : Simpterm.term =
  let open Simpterm in
  let abid = Elab.Term.gen_binder_id () in
  let bbid = Elab.Term.gen_binder_id () in
  let hbid = Elab.Term.gen_binder_id () in
  let times (n : int) (m : term) : term =
    List.fold_left (fun acc _ -> App (App (Name "Add", acc), m)) m (List.init (n-1) Fun.id)
  in
  let na = times n (Bvar abid) in
  let nb = times n (Bvar bbid) in
  let proof_ty =
    Arrow
      ( Some "a",
        abid,
        Name "Measure",
        Arrow
          ( Some "b",
            bbid,
            Name "Measure",
            Arrow
              ( None,
                hbid,
                App (App (Name "Lt", na), nb),
                App (App (Name "Lt", Bvar abid), Bvar bbid) ) ) )
  in
  (* TODO: Implement the actual proof *)
  (* tactic proof for n=5:
  
Theorem LtAddLeft : ∀ (a b c : Measure), a < b → c + a < c + b
Proof.
intros a b c ab.
rewrite (AddComm c a).
rewrite (AddComm c b).
exact (LtAdd _ _ _ ab).
Qed.

Theorem add_lt_add : ∀ (a b c d : Measure), a < b → c < d → a + c < b + d
Proof.
intros a b c d ab cd.
have h1 (a + c < b + c).
    apply (LtAdd _ _ _).
    exact ab.
have h2 (b + c < b + d).
    apply (LtAddLeft _ _ _).
    exact cd.
exact (LtTrans _ _ _ h1 h2).
Qed.

Theorem cancel_five : ∀ (a b : Measure), a + a + a + a + a < b + b + b + b + b → a < b
Proof.
intros a b h.
cases (LtTricot a b) hab.
exact hab.

cases hab hab1.
apply (False.elim _).
have hab2 _. exact (add_lt_add _ _ _ _ hab1 hab1).
have hab3 _. exact (add_lt_add _ _ _ _ hab2 hab1).
have hab4 _. exact (add_lt_add _ _ _ _ hab3 hab1).
have hab5 _. exact (add_lt_add _ _ _ _ hab4 hab1).
exact (LtAntisymm _ _ hab5 h).

apply (False.elim _).
apply (LtNe _ _ h).
rewrite hab1.
reflexivity.
Qed.

  *)
  App (Name "sorry", proof_ty)

