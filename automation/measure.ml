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
