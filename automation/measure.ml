(* canonical order for Measures *)
(*
there are a few things that are Measures (infertype on it returns Measure)
Zero
RightAngle
Add a b
Length a b
Angle a b c
Area a b c
bvar id
f x where f : _ -> Measure not definitionally one of the above (maybe we can just error out in this case)

ok we want the normalization to actually account for things
like the point of having an order is to not have to think about commutativity
but we also want to not think about associativity which involves flattening the Adds
there was an algorithm for this
so we need an order on the summands which is every measure except Add
say
- Zero
- RightAngle
- Length a b
- Angle a b c
- Area a b c
- bvar id
where Length a b is lexicographically ordered
ok what does lexicographic order on a b c look like (which are points)
need an order on points, which are:
- bvar id
hm. thats easy.

uhhhhh ok actually angle complicates things
we don't permute angle arbitrarily, only angle a b c = angle c b a
so normal form is just where a ≤ c
length and area just sorted
ok cool
ok also unless we change the axiom we can only get angle a b c = angle c b a if we also have proofs of a ≠ b and a ≠ c
we can keep a "database" of all the ≠ conditions we have for all angles
thats for later
oh and if we ever implement congruence closure on points, we also have to consider this inequality database
*)

(** identified and ordered by default OCaml lexicographic ordering *)
type summand =
  | Zero
  | RightAngle
  | Length of int * int
  | Angle of int * int * int
  | Area of int * int * int
  | Bvar of int

(** call whnf on tm before calling to_summand tm *)
let to_summand (tm : Elab.Term.term) : summand option =
  let open Simpterm in
  match to_simpterm tm with
  | Name "Zero" -> Some Zero
  | Name "RightAngle" -> Some RightAngle
  | App (App (Name "Length", Bvar a), Bvar b) -> Some (Length (a, b))
  | App (App (App (Name "Angle", Bvar a), Bvar b), Bvar c) -> Some (Angle (a, b, c))
  | App (App (App (Name "Area", Bvar a), Bvar b), Bvar c) -> Some (Area (a, b, c))
  | Bvar id -> Some (Bvar id)
  | _ -> None

let summand_to_term (s : summand) : Simpterm.term =
  let open Simpterm in
  match s with
  | Zero -> Name "Zero"
  | RightAngle -> Name "RightAngle"
  | Length (a, b) -> App (App (Name "Length", Bvar a), Bvar b)
  | Angle (a, b, c) -> App (App (App (Name "Angle", Bvar a), Bvar b), Bvar c)
  | Area (a, b, c) -> App (App (App (Name "Area", Bvar a), Bvar b), Bvar c)
  | Bvar id -> Bvar id

(** A measure is a sum of summands once the additions have been left-associated. proof is
    the proof that summands_to_term summands = original. *)
type measure = {
  summands : summand list;
  original : Simpterm.term;
  proof : Simpterm.term;  (** the proof that summands_to_term summands = original *)
}

let summands_to_term (summands : summand list) : Simpterm.term =
  let open Simpterm in
  (* wildy inefficient but oh well *)
  let summand_terms = List.map (fun x -> summand_to_term x) summands in
  match summand_terms with
  | [] -> failwith "summands_to_term: empty summand list"
  | [ t ] -> t
  | t :: ts -> List.fold_left (fun acc t -> App (App (Name "Add", acc), t)) t ts

(** returns proof of t = t *)
let refl (t : Simpterm.term) : Simpterm.term =
  App (App (Name "Eq.intro", Name "Measure"), t)

let proof_symm (m : measure) : Simpterm.term =
  let open Simpterm in
  if summands_to_term m.summands = m.original then refl m.original
  else
    apps
      (Name "Eq.symm")
      [ Name "Measure"; summands_to_term m.summands; m.original; m.proof ]

let measure_to_term (m : measure) : Elab.Term.term =
  Simpterm.from_simpterm (summands_to_term m.summands)

(** tm should not have holes and should be fully beta and delta reduced *)
let to_measure (tm : Simpterm.term) : measure option =
  let open Simpterm in
  (* ill call "right-normal form" when it's Add(something, something that isn't add) *)
  (* returns the right normal form and the proof it equals the argument *)
  let rec right_normal (tm : term) : term * term =
    match tm with
    | App (App (Name "Add", t1), App (App (Name "Add", t2), t3)) ->
        let new_left = App (App (Name "Add", t1), t2) in
        let new_term = App (App (Name "Add", new_left), t3) in
        let new_term_normal, proof = right_normal new_term in
        (* proof is proof that new_term_normal = new_term *)
        (* need to return proof that new_term_normal = tm *)
        (* eqtrans of proof and AddAssoc t1 t2 t3 *)
        let add_assoc_proof = apps (Name "AddAssoc") [ t1; t2; t3 ] in
        let res_proof =
          apps
            (Name "EqTrans")
            [ Name "Measure"; new_term_normal; new_term; tm; proof; add_assoc_proof ]
        in
        (new_term_normal, res_proof)
    | _ -> (tm, refl tm)
  in

  let rec assoc_normal (tm : term) : term * term =
    match right_normal tm with
    | (App (App (Name "Add", t1), t2) as t), proof ->
        let t1_normal, proof1 = assoc_normal t1 in
        (* proof : t1 + t2 = tm *)
        (* proof1 : t1_normal = t1 *)
        (* need to return proof that t1_normal + t2 = tm *)
        if t1_normal = t1 then (t, proof)
        else
          ( App (App (Name "Add", t1_normal), t2),
            apps (Name "AddLeftRewrite") [ t1; t1_normal; t2; tm; proof; proof1 ] )
    | t, proof -> (t, proof)
  in

  let tm_normal, proof = assoc_normal tm in

  let rec get_summands (tm : term) : summand list option =
    match tm with
    | App (App (Name "Add", t1), t2) ->
        (* i love functional slop *)
        Option.bind
          (to_summand (from_simpterm t2))
          (fun s2 -> get_summands t1 |> Option.map (fun s1 -> s1 @ [ s2 ]))
    | t -> to_summand (from_simpterm t) |> Option.map (fun x -> [ x ])
  in

  Option.map (fun summands -> { summands; original = tm; proof }) (get_summands tm_normal)

let measure_of_summands (summands : summand list) : measure =
  let tm = summands_to_term summands in
  { summands; original = tm; proof = refl tm }

(** rewrites the first i summands of m as new_summands, where proof is a proof of
    m.summands[0..=i-1] = new_summands. this might crash and burn if new_summands = [] and
    i = length m.summands so uhh maybe dont do that *)
let congr (m : measure) (i : int) (new_summands : summand list) (proof : Simpterm.term) :
    measure =
  let open Simpterm in
  let new_summands_term = summands_to_term new_summands in
  let old_summands_term = summands_to_term (List.take i m.summands) in
  let bid = Elab.Term.gen_binder_id () in
  let motive_sum =
    List.fold_left
      (fun acc s -> App (App (Name "Add", acc), summand_to_term s))
      (Bvar bid)
      (List.drop i m.summands)
  in

  let motive =
    Fun
      ( None,
        bid,
        Name "Measure",
        App (App (App (Name "Eq", Name "Measure"), motive_sum), m.original) )
  in
  let congr_proof =
    apps
      (Name "Eq.elim")
      [ Name "Measure"; old_summands_term; motive; m.proof; new_summands_term; proof ]
  in
  {
    summands = new_summands @ List.drop i m.summands;
    original = m.original;
    proof = congr_proof;
  }

(** rewrites the i-th summand of m as new_summand, where proof is a proof of m.summands[i]
    = new_summand *)
let rewrite_i (m : measure) (i : int) (new_summand : summand) (proof : Simpterm.term) :
    measure =
  let open Simpterm in
  let a_list = List.take i m.summands in
  let new_sublist = a_list @ [ new_summand ] in
  let bigproof =
    if i = 0 then proof
    else
      apps
        (Name "AddCongLeft")
        [
          summand_to_term (List.nth m.summands i);
          summand_to_term new_summand;
          summands_to_term a_list;
          proof;
        ]
  in
  congr m (i + 1) new_sublist bigproof

let normalize_summand (m : measure) (i : int) : measure =
  let open Simpterm in
  match List.nth m.summands i with
  | Length (a, b) when a > b ->
      rewrite_i m i (Length (b, a)) (apps (Name "length_symm") [ Bvar a; Bvar b ])
      (* todo: handle other summand types *)
  | _ -> m

let normalize_summands (m : measure) : measure =
  List.fold_left
    (fun m i -> normalize_summand m i)
    m
    (List.init (List.length m.summands) (fun i -> i))

(** swaps summand i and i+1 in a measure updating the proof. i and i+1 must be valid
    indices *)
let swap_adjacent (m : measure) (i : int) : measure =
  let open Simpterm in
  let a_list = List.take i m.summands in
  let new_sublist = a_list @ [ List.nth m.summands (i + 1); List.nth m.summands i ] in
  let proof =
    if i = 0 then
      apps
        (Name "AddComm")
        [
          summand_to_term (List.nth m.summands i);
          summand_to_term (List.nth m.summands (i + 1));
        ]
    else
      apps
        (Name "AddRightComm")
        [
          summands_to_term a_list;
          summand_to_term (List.nth m.summands i);
          summand_to_term (List.nth m.summands (i + 1));
        ]
  in
  congr m (i + 2) new_sublist proof

let sort (m : measure) : measure =
  let rec bubblesort (m : measure) (current : int) (target : int) : measure =
    if current = target then if target = 0 then m else bubblesort m 0 (target - 1)
    else if List.nth m.summands current > List.nth m.summands (current + 1) then
      bubblesort (swap_adjacent m current) (current + 1) target
    else bubblesort m (current + 1) target
  in
  bubblesort m 0 (List.length m.summands - 1)

let rec cancel_zeros (m : measure) : measure =
  let open Simpterm in
  match m.summands with
  | Zero :: a :: _ ->
      congr m 2 [ a ] (App (Name "ZeroAdd", summand_to_term a)) |> cancel_zeros
  | _ -> m

let normalize_measure (m : measure) : measure =
  m |> normalize_summands |> sort |> cancel_zeros

(** returns a proof of t1 = t2 if they are definitionally equal after sorting *)
let normalized_rfl (t1 : summand list) (t2 : summand list) : Simpterm.term =
  let open Simpterm in
  let m1 = cancel_zeros (sort (measure_of_summands t1)) in
  let m2 = cancel_zeros (sort (measure_of_summands t2)) in
  (* sanity check *)
  if m1.summands = m2.summands then
    let tnorm = summands_to_term m1.summands in
    (* m1.proof : tnorm = t1 *)
    (* m2.proof : tnorm = t2 *)
    apps
      (Name "EqTrans")
      [
        Name "Measure";
        summands_to_term t1;
        tnorm;
        summands_to_term t2;
        proof_symm m1;
        m2.proof;
      ]
  else failwith "normalized_rfl: summand lists are not equal after normalization"
