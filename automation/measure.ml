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

let summand_to_term (s : summand) : Elab.Term.term =
  let open Simpterm in
  let res =
    match s with
    | Zero -> Name "Zero"
    | RightAngle -> Name "RightAngle"
    | Length (a, b) -> App (App (Name "Length", Bvar a), Bvar b)
    | Angle (a, b, c) -> App (App (App (Name "Angle", Bvar a), Bvar b), Bvar c)
    | Area (a, b, c) -> App (App (App (Name "Area", Bvar a), Bvar b), Bvar c)
    | Bvar id -> Bvar id
  in
  from_simpterm res

let order (s : summand) : int * int * int * int =
  match s with
  | Zero -> (0, 0, 0, 0)
  | RightAngle -> (1, 0, 0, 0)
  | Length (a, b) -> (2, a, b, 0)
  | Angle (a, b, c) -> (3, a, b, c)
  | Area (a, b, c) -> (4, a, b, c)
  | Bvar id -> (5, id, 0, 0)

(** A measure is a sum of summands once the additions have been left-associated. proof is
    the proof that measure_to_term this = original. *)
type measure = {
  summands : summand list;
  original : Simpterm.term;
  proof : Simpterm.term;
}

let measure_to_term (m : measure) : Elab.Term.term =
  let open Simpterm in
  (* wildy inefficient but oh well *)
  let summand_terms = List.map (fun x -> to_simpterm (summand_to_term x)) m.summands in
  let res =
    match summand_terms with
    | [] -> Name "Zero"
    | [ t ] -> t
    | t :: ts -> List.fold_left (fun acc t -> App (App (Name "Add", acc), t)) t ts
  in
  from_simpterm res

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
        (App (App (Name "Add", t1_normal), t2), apps (Name "AddLeftRewrite") [ t1; t1_normal; t2; tm; proof; proof1 ])
    | t, proof -> (t, proof)
  in

  let tm_normal, proof = assoc_normal tm in

  print_endline ("tm_normal: " ^ Elab.Pretty.term_to_string (Elab.Interface.create ()) (from_simpterm tm_normal));

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
