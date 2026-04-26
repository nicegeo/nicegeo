open Simpterm
open Measure

(** decides (in)equalities on Measures using Fourier–Motzkin elimination (at least that's
    the goal) *)

(** produces a proof of type ∀ (a b : Measure), n * a < n * b → a < b where n * a denotes
    a + a + ... + a (n times) *)
let lt_cancel_mul (n : int) : term =
  let abid = Elab.Term.gen_binder_id () in
  let bbid = Elab.Term.gen_binder_id () in
  let hbid = Elab.Term.gen_binder_id () in
  let times (n : int) (m : term) : term =
    List.fold_left
      (fun acc _ -> App (App (Name "Add", acc), m))
      m
      (List.init (n - 1) Fun.id)
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

type relation =
  | Lt
  | Le
  | Eq

(** constraint is an ocaml keyword... *)
type constrain = {
  r : relation;
  lhs : summand list;
  rhs : summand list;
  proof : term; (* proof of lhs (R) rhs *)
}

let relation_to_term (r : relation) : term =
  match r with Lt -> Name "Lt" | Le -> Name "Le" | Eq -> App (Name "Eq", Name "Measure")

let constrain_ty (c : constrain) : term =
  App (App (relation_to_term c.r, summands_to_term c.lhs), summands_to_term c.rhs)

(** tm should be of type rel lhs rhs. proof should be type lhs = new_lhs. returns a proof
    of type rel new_lhs rhs *)
let rewrite_lhs_proof (tm : term) (rel : term) (lhs : term) (rhs : term)
    (new_lhs : summand list) (proof : term) : term =
  let bid = Elab.Term.gen_binder_id () in
  let motive = Fun (None, bid, Name "Measure", App (App (rel, Bvar bid), rhs)) in
  apps
    (Name "Eq.elim")
    [ Name "Measure"; lhs; motive; tm; summands_to_term new_lhs; proof ]

(** proof should be type c.lhs = new_lhs *)
let rewrite_lhs (c : constrain) (new_lhs : summand list) (proof : term) : constrain =
  {
    lhs = new_lhs;
    rhs = c.rhs;
    r = c.r;
    proof =
      rewrite_lhs_proof
        c.proof
        (relation_to_term c.r)
        (summands_to_term c.lhs)
        (summands_to_term c.rhs)
        new_lhs
        proof;
  }

(** proof should be type rhs = new_rhs *)
let rewrite_rhs_proof (tm : term) (rel : term) (lhs : term) (rhs : term)
    (new_rhs : summand list) (proof : term) : term =
  let bid = Elab.Term.gen_binder_id () in
  let motive = Fun (None, bid, Name "Measure", App (App (rel, lhs), Bvar bid)) in
  apps
    (Name "Eq.elim")
    [ Name "Measure"; rhs; motive; tm; summands_to_term new_rhs; proof ]

(** proof should be type c.rhs = new_rhs *)
let rewrite_rhs (c : constrain) (new_rhs : summand list) (proof : term) : constrain =
  {
    lhs = c.lhs;
    rhs = new_rhs;
    r = c.r;
    proof =
      rewrite_rhs_proof
        c.proof
        (relation_to_term c.r)
        (summands_to_term c.lhs)
        (summands_to_term c.rhs)
        new_rhs
        proof;
  }

let sort_sides (c : constrain) : constrain =
  let new_lhs = sort (measure_of_summands c.lhs) in
  let c = rewrite_lhs c new_lhs.summands (proof_symm new_lhs) in
  let new_rhs = sort (measure_of_summands c.rhs) in
  rewrite_rhs c new_rhs.summands (proof_symm new_rhs)

let cancel_ij (c : constrain) (i : int) (j : int) : constrain =
  let common = List.nth c.lhs i in
  let new_lhs = List.take i c.lhs @ List.drop (i + 1) c.lhs in
  let lhs_rewritten = new_lhs @ [ common ] in
  let c = rewrite_lhs c lhs_rewritten (sorted_rfl c.lhs lhs_rewritten) in
  let new_rhs = List.take j c.rhs @ List.drop (j + 1) c.rhs in
  let rhs_rewritten = new_rhs @ [ common ] in
  let c = rewrite_rhs c rhs_rewritten (sorted_rfl c.rhs rhs_rewritten) in

  let proof = match c.r with
  | Eq -> apps (Name "AddCancel") [ summands_to_term new_lhs; summands_to_term new_rhs; summand_to_term common; c.proof ] 
  | Lt -> apps (Name "LtCancelRight") [ summands_to_term new_lhs; summands_to_term new_rhs; summand_to_term common; c.proof ]
  | Le -> failwith "not implemented"
  in

  let c = { lhs = new_lhs; rhs = new_rhs; r = c.r; proof } in
  c

(** simplifies a constrain so that there's no like terms on both sides *)
let simp_constrain (c : constrain) : constrain =
  let c = sort_sides c in
  (* linear search thing *)
  let rec find_common (c : constrain) (i : int) (j : int) : constrain =
    if i >= List.length c.lhs || j >= List.length c.rhs then c
    else if List.nth c.lhs i = List.nth c.rhs j then
      let c = cancel_ij c i j in
      find_common c i j
    else if List.nth c.lhs i < List.nth c.rhs j then find_common c (i + 1) j
    else find_common c i (j + 1)
  in
  find_common c 0 0

let destruct_relation_ty (tm : term) : (relation * term * term) option =
  match tm with
  | App (App (rel, lhs), rhs) -> (
      match rel with
      | Name "Lt" -> Some (Lt, lhs, rhs)
      | Name "Le" -> Some (Le, lhs, rhs)
      | App (Name "Eq", Name "Measure") -> Some (Eq, lhs, rhs)
      | _ -> None)
  (* handle head-reduced Le a b := Lt b a -> False *)
  | Arrow (_, _, App (App (Name "Lt", rhs), lhs), Name "False") -> Some (Le, lhs, rhs)
  | _ -> None

let create_constrain (ty : term) (proof : term) : constrain option =
  Option.bind (destruct_relation_ty ty) (fun (r, lhs, rhs) ->
      Option.bind (to_measure lhs) (fun lhs_meas ->
          let lhs_norm = normalize_measure lhs_meas in
          (* lhs_norm.proof : lhs_norm = lhs *)
          let proof =
            rewrite_lhs_proof
              proof
              (relation_to_term r)
              lhs
              rhs
              lhs_norm.summands
              (proof_symm lhs_norm)
          in
          Option.bind (to_measure rhs) (fun rhs_meas ->
              let rhs_norm = normalize_measure rhs_meas in
              (* rhs_norm.proof : rhs_norm = rhs *)
              let proof =
                rewrite_rhs_proof
                  proof
                  (relation_to_term r)
                  (summands_to_term lhs_norm.summands)
                  rhs
                  rhs_norm.summands
                  (proof_symm rhs_norm)
              in
              Some { r; lhs = lhs_norm.summands; rhs = rhs_norm.summands; proof })))
