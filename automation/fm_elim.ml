open Simpterm
open Measure

(** decides (in)equalities on Measures using Fourier–Motzkin elimination (at least that's
    the goal) *)

let times (n : int) (m : term) : term =
  List.fold_left
    (fun acc _ -> App (App (Name "Add", acc), m))
    m
    (List.init (n - 1) Fun.id)

(** produces a proof of type ∀ (a b : Measure), a < b → n * a < n * b where n * a denotes
    a + a + ... + a (n times) *)
let lt_mul (n : int) : term =
  let abid = Elab.Term.gen_binder_id () in
  let bbid = Elab.Term.gen_binder_id () in
  let hbid = Elab.Term.gen_binder_id () in

  let na = times n (Bvar abid) in
  let nb = times n (Bvar bbid) in
  let _proof_ty =
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
                App (App (Name "Lt", Bvar abid), Bvar bbid),
                App (App (Name "Lt", na), nb) ) ) )
  in

  (* creates a proof of n * a < n * b *)
  let rec build_proof (n : int) : term =
    if n = 1 then Bvar hbid
    else
      let smaller_proof = build_proof (n - 1) in
      let an1 = times (n - 1) (Bvar abid) in
      let bn1 = times (n - 1) (Bvar bbid) in
      apps
        (Name "add_lt_add")
        [ an1; bn1; Bvar abid; Bvar bbid; smaller_proof; Bvar hbid ]
  in

  Fun
    ( Some "a",
      abid,
      Name "Measure",
      Fun
        ( Some "b",
          bbid,
          Name "Measure",
          Fun (None, hbid, App (App (Name "Lt", Bvar abid), Bvar bbid), build_proof n) )
    )

(** produces a proof of type ∀ (a b : Measure), a = b → n * a = n * b where n * a denotes
    a + a + ... + a (n times) *)
let eq_mul (n : int) : term =
  let abid = Elab.Term.gen_binder_id () in
  let bbid = Elab.Term.gen_binder_id () in
  let hbid = Elab.Term.gen_binder_id () in

  let na = times n (Bvar abid) in

  let motive_bid = Elab.Term.gen_binder_id () in
  (* n*a = n*x *)
  let motive_body =
    App (App (App (Name "Eq", Name "Measure"), na), times n (Bvar motive_bid))
  in
  let motive = Fun (None, motive_bid, Name "Measure", motive_body) in

  Fun
    ( Some "a",
      abid,
      Name "Measure",
      Fun
        ( Some "b",
          bbid,
          Name "Measure",
          Fun
            ( None,
              hbid,
              App (App (App (Name "Eq", Name "Measure"), Bvar abid), Bvar bbid),
              apps
                (Name "Eq.elim")
                [ Name "Measure"; Bvar abid; motive; refl na; Bvar bbid; Bvar hbid ] ) )
    )

(** produces a proof of type ∀ (a b : Measure), n * a < n * b → a < b where n * a denotes
    a + a + ... + a (n times) *)
let lt_cancel_mul (n : int) : term =
  let abid = Elab.Term.gen_binder_id () in
  let bbid = Elab.Term.gen_binder_id () in
  let hbid = Elab.Term.gen_binder_id () in

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

let normalize_sides (c : constrain) : constrain =
  let new_lhs = normalize_measure (measure_of_summands c.lhs) in
  let c = rewrite_lhs c new_lhs.summands (proof_symm new_lhs) in
  let new_rhs = normalize_measure (measure_of_summands c.rhs) in
  rewrite_rhs c new_rhs.summands (proof_symm new_rhs)

(** don't call this on Zero *)
let cancel_ij (c : constrain) (i : int) (j : int) : constrain =
  let common = List.nth c.lhs i in
  let new_lhs = List.take i c.lhs @ List.drop (i + 1) c.lhs in
  let new_lhs = if new_lhs = [] then [ Zero ] else new_lhs in
  let lhs_rewritten = new_lhs @ [ common ] in
  let c = rewrite_lhs c lhs_rewritten (normalized_rfl c.lhs lhs_rewritten) in
  let new_rhs = List.take j c.rhs @ List.drop (j + 1) c.rhs in
  let new_rhs = if new_rhs = [] then [ Zero ] else new_rhs in
  let rhs_rewritten = new_rhs @ [ common ] in
  let c = rewrite_rhs c rhs_rewritten (normalized_rfl c.rhs rhs_rewritten) in

  let proof =
    match c.r with
    | Eq ->
        apps
          (Name "AddCancel")
          [
            summands_to_term new_lhs;
            summands_to_term new_rhs;
            summand_to_term common;
            c.proof;
          ]
    | Lt ->
        apps
          (Name "LtCancelRight")
          [
            summands_to_term new_lhs;
            summands_to_term new_rhs;
            summand_to_term common;
            c.proof;
          ]
    | Le -> failwith "not implemented"
  in

  let c = { lhs = new_lhs; rhs = new_rhs; r = c.r; proof } in
  c

(** simplifies a constrain so that there's no like terms on both sides *)
let simp_constrain (c : constrain) : constrain =
  let c = normalize_sides c in
  (* linear search thing *)
  let rec find_common (c : constrain) (i : int) (j : int) : constrain =
    if i >= List.length c.lhs || j >= List.length c.rhs || c.lhs = [Zero] || c.rhs = [Zero] then c
    else if List.nth c.lhs i = List.nth c.rhs j then
      let c = cancel_ij c i j in
      find_common c i j
    else if List.nth c.lhs i < List.nth c.rhs j then find_common c (i + 1) j
    else find_common c i (j + 1)
  in
  find_common c 0 0

let add_one_both_sides (c : constrain) (s : summand) : constrain =
  let new_lhs = c.lhs @ [ s ] in
  let new_rhs = c.rhs @ [ s ] in
  let proof =
    match c.r with
    | Eq ->
        apps
          (Name "AddCongRight")
          [ summands_to_term c.lhs; summands_to_term c.rhs; summand_to_term s; c.proof ]
    | Lt ->
        apps
          (Name "LtAdd")
          [ summands_to_term c.lhs; summands_to_term c.rhs; summand_to_term s; c.proof ]
    | Le -> failwith "not implemented"
  in
  { lhs = new_lhs; rhs = new_rhs; r = c.r; proof }

let add_both_sides (c : constrain) (ss : summand list) : constrain =
  List.fold_left add_one_both_sides c ss

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

let coefficient (summands : summand list) (s : summand) : int =
  List.fold_left (fun acc summand -> if summand = s then acc + 1 else acc) 0 summands

(* euclidean algorithm for gcd *)
let rec gcd a b = if b = 0 then abs a else gcd b (a mod b)

(* lcm using gcd *)
let lcm a b = if a = 0 || b = 0 then 0 else abs (a * b) / gcd a b

(** multiplies a constrain by a scalar (so a < b becomes n * a < n * b up to
    normalization) *)
let mult_constrain (c : constrain) (n : int) : constrain =
  let lhs_tm = summands_to_term c.lhs in
  let rhs_tm = summands_to_term c.rhs in
  let nlhs = times n lhs_tm in
  let nrhs = times n rhs_tm in
  let proof =
    match c.r with
    | Eq -> apps (eq_mul n) [ lhs_tm; rhs_tm; c.proof ]
    | Lt -> apps (lt_mul n) [ lhs_tm; rhs_tm; c.proof ]
    | Le -> failwith "mult_constrain Le not implemented"
  in
  create_constrain (App (App (relation_to_term c.r, nlhs), nrhs)) proof |> Option.get

(** returns (a, b) such that s1 + a = s2 + b. may return empty lists *)
let level_sums (s1 : summand list) (s2 : summand list) : summand list * summand list =
  let rec go s1 s2 =
    match s1 with
    | [] -> (s2, [])
    | s :: s1' -> (
        match List.find_index (fun x -> x = s) s2 with
        | None ->
            let a, b = go s1' s2 in
            (a, s :: b)
        | Some idx ->
            let s2' = List.take idx s2 @ List.drop (idx + 1) s2 in
            go s1' s2')
  in
  go s1 s2

(** returns (c1', c2') where c1'.c1right = c2'.c2right and the other sides do not contain
    atom by multiplying c1 and c2 to match their coefficients of atom and adding the
    missing terms from the other side. precondition: c1 and c2 are simplified, c1.c1right
    and c2.c2right are the sides to match that contain atom *)
let match_sides_to_cancel (c1 : constrain) (c1right : bool) (c2 : constrain)
    (c2right : bool) (atom : summand) : constrain * constrain =
  let side c right = if right then c.rhs else c.lhs in
  (* match coefficients by multiplying up to lcm *)
  let coef_c1 = coefficient (side c1 c1right) atom in
  let coef_c2 = coefficient (side c2 c2right) atom in
  let common_coef = lcm coef_c1 coef_c2 in
  let c1_mult = mult_constrain c1 (common_coef / coef_c1) in
  let c2_mult = mult_constrain c2 (common_coef / coef_c2) in

  (* find union of the middle terms *)
  let c1_diff, c2_diff = level_sums (side c1_mult c1right) (side c2_mult c2right) in
  let final_c1 = add_both_sides c1_mult c1_diff in
  let final_c2 = add_both_sides c2_mult c2_diff in

  (sort_sides final_c1, sort_sides final_c2)

(** returns a new constrain list without atom by rewriting all other constrains using the
    equality cs[i]. cs[i] must contain atom, atom must not be Zero, all constrains must be
    simplified *)
let elim_eq (cs : constrain list) (i : int) (atom : summand) : constrain list =
  let eq = List.nth cs i in
  if eq.r <> Eq then failwith "elim_eq: cs[i] is not an equality"
  else
    let eq =
      if List.exists (fun s -> s = atom) eq.rhs then
        (* flip eq *)
        {
          r = Eq;
          lhs = eq.rhs;
          rhs = eq.lhs;
          proof =
            apps
              (Name "Eq.symm")
              [
                Name "Measure"; summands_to_term eq.lhs; summands_to_term eq.rhs; eq.proof;
              ];
        }
      else if List.exists (fun s -> s = atom) eq.lhs then eq
      else failwith "elim_eq: atom not found in cs[i]"
    in
    List.map
      (fun c ->
        if List.exists (fun s -> s = atom) c.lhs then
          let final_eq, matching_c = match_sides_to_cancel eq false c false atom in
          (* rewrite matching_c using final_eq *)
          rewrite_lhs matching_c final_eq.rhs final_eq.proof
        else if List.exists (fun s -> s = atom) c.rhs then
          let final_eq, matching_c = match_sides_to_cancel eq false c true atom in
          (* rewrite matching_c using final_eq *)
          rewrite_rhs matching_c final_eq.rhs final_eq.proof
        else c)
      (List.take i cs @ List.drop (i + 1) cs)

(** eliminates all occurrences of atom from the list of constrains. constrains must not
    have any Eqs mentioning atom and must be simplified *)
let elim_atom (cs : constrain list) (atom : summand) : constrain list =
  let cs, unmentioned =
    List.partition
      (fun c ->
        List.exists (fun s -> s = atom) c.lhs || List.exists (fun s -> s = atom) c.rhs)
      cs
  in
  let cs_lower, cs_upper =
    List.partition (fun c -> List.exists (fun s -> s = atom) c.lhs) cs
  in
  List.flatten
    (List.map
       (fun c_lower ->
         List.map
           (fun c_upper ->
             (* c_upper.rhs mentions atom, c_lower.lhs mentions atom *)
             let final_c_lower, final_c_upper =
               match_sides_to_cancel c_lower false c_upper true atom
             in
             let rel, proof =
               match (final_c_lower.r, final_c_upper.r) with
               | Lt, Lt ->
                   ( Lt,
                     apps
                       (Name "LtTrans")
                       [
                         summands_to_term final_c_upper.lhs;
                         summands_to_term final_c_upper.rhs;
                         summands_to_term final_c_lower.rhs;
                         final_c_upper.proof;
                         final_c_lower.proof;
                       ] )
               | _ -> failwith "elim_atom: not implemented for non-Lt relations"
             in
             { r = rel; lhs = final_c_upper.lhs; rhs = final_c_lower.rhs; proof })
           cs_upper)
       cs_lower)
  @ unmentioned

let rec try_prove_false (cs : constrain list) : term option =
  (* main loop *)
  let cs = List.map simp_constrain cs in
  (* is there a contradiction? (a < 0) *)
  match
    List.find_map
      (fun c ->
        if c.r = Lt then
          match (c.lhs, c.rhs) with
          | lhs, [Zero] -> Some (apps (Name "LtZero") [ summands_to_term lhs; c.proof ])
          | _ -> None
        else None)
      cs
  with
  | Some proof -> Some proof
  | None -> (
      (* find an atom to eliminate *)
      (* search for Eqs first *)
      match
        List.find_mapi
          (fun i c ->
            match c with
            | { r = Eq; lhs = s :: _; _ } | { r = Eq; rhs = s :: _; _ } -> Some (i, s)
            | _ -> None)
          cs
      with
      | Some (i, atom) ->
          let cs = elim_eq cs i atom in
          try_prove_false cs
      | None -> (
          (* no Eqs, find any atom *)
          let atom =
            List.find_map
              (fun c ->
                match c with
                | { lhs = s :: _; _ } | { rhs = s :: _; _ } -> Some s
                | _ -> None)
              cs
          in
          match atom with
          | Some atom ->
              let cs = elim_atom cs atom in
              try_prove_false cs
          | None -> None))
