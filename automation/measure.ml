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
*)

type summand =
  | Zero
  | RightAngle
  | Length of (int * int)
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

let order (s : summand) : int * int * int * int =
  match s with
  | Zero -> (0, 0, 0, 0)
  | RightAngle -> (1, 0, 0, 0)
  | Length (a, b) -> (2, a, b, 0)
  | Angle (a, b, c) -> (3, a, b, c)
  | Area (a, b, c) -> (4, a, b, c)
  | Bvar id -> (5, id, 0, 0)

(** A measure is a sum of summands once the additions have been left-associated. proof is
    the proof that summands_to_term summands = original. *)
type measure = {
  summands : summand list;
  original : Simpterm.term;
  proof : Simpterm.term;
}

let summands_to_term (summands : summand list) : Simpterm.term =
  let open Simpterm in
  (* wildy inefficient but oh well *)
  let summand_terms = List.map (fun x -> summand_to_term x) summands in
  match summand_terms with
  | [] -> Name "Zero"
  | [ t ] -> t
  | t :: ts -> List.fold_left (fun acc t -> App (App (Name "Add", acc), t)) t ts

let measure_to_term (m : measure) : Elab.Term.term =
  Simpterm.from_simpterm (summands_to_term m.summands)

(** returns proof of t = t *)
let refl (t : Simpterm.term) : Simpterm.term =
  App (App (Name "Eq.intro", Name "Measure"), t)

let to_measure (tm : Elab.Term.term) : measure option =
  let open Simpterm in
  let tm = to_simpterm tm in
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
    | App (App (Name "Add", t1), t2), proof ->
        let t1_normal, proof1 = assoc_normal t1 in
        (* proof : t1 + t2 = tm *)
        (* proof1 : t1_normal = t1 *)
        (* need to return proof that t1_normal + t2 = tm *)
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

(** rewrites the first i summands of m as new_summands, where proof is a proof of
    m.summands[0..=i-1] = new_summands *)
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
  
(** swaps summand i and i+1 in a measure updating the proof. i and i+1 must be valid indices *)
let swap_adjacent (m : measure) (i : int) : measure =
  let open Simpterm in
  let a_list = (List.take i m.summands) in
  let new_sublist = a_list @ [List.nth m.summands (i + 1); List.nth m.summands i] in
  let proof = if i = 0 then
    apps (Name "AddComm") [summand_to_term (List.nth m.summands i); summand_to_term (List.nth m.summands (i + 1))]
  else
    apps (Name "AddRightComm") [summands_to_term a_list; summand_to_term (List.nth m.summands i); summand_to_term (List.nth m.summands (i + 1))]
  in
  congr m (i + 2) new_sublist proof

let sort (m : measure) : measure =
  let rec bubblesort (m : measure) (current : int) (target : int) : measure =
    if current = target then (
      if target = 0 then m
      else bubblesort m 0 (target - 1)
    ) else if order (List.nth m.summands current) > order (List.nth m.summands (current + 1)) then
      bubblesort (swap_adjacent m current) (current + 1) target
    else
      bubblesort m (current + 1) target
  in
  bubblesort m 0 (List.length m.summands - 1)

