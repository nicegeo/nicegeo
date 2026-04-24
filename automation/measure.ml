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
  let open Elab.Term in
  match tm.inner with
  | Name "Zero" -> Some Zero
  | Name "RightAngle" -> Some RightAngle
  | App
      ( { inner = App ({ inner = Name "Length"; _ }, { inner = Bvar a; _ }); _ },
        { inner = Bvar b; _ } ) ->
      Some (Length (a, b))
  | App
      ( {
          inner =
            App
              ( { inner = App ({ inner = Name "Angle"; _ }, { inner = Bvar a; _ }); _ },
                { inner = Bvar b; _ } );
          _;
        },
        { inner = Bvar c; _ } ) ->
      Some (Angle (a, b, c))
  | App
      ( {
          inner =
            App
              ( { inner = App ({ inner = Name "Area"; _ }, { inner = Bvar a; _ }); _ },
                { inner = Bvar b; _ } );
          _;
        },
        { inner = Bvar c; _ } ) ->
      Some (Area (a, b, c))
  | Bvar id -> Some (Bvar id)
  | _ -> None

let summand_to_term (s : summand) : Elab.Term.term =
  let open Elab.Proofstate in
  match s with
  | Zero -> mk_name "Zero"
  | RightAngle -> mk_name "RightAngle"
  | Length (a, b) -> mk_app (mk_app (mk_name "Length") (mk_bvar a)) (mk_bvar b)
  | Angle (a, b, c) ->
      mk_app (mk_app (mk_app (mk_name "Angle") (mk_bvar a)) (mk_bvar b)) (mk_bvar c)
  | Area (a, b, c) ->
      mk_app (mk_app (mk_app (mk_name "Area") (mk_bvar a)) (mk_bvar b)) (mk_bvar c)
  | Bvar id -> mk_bvar id

let order (s : summand) : int * int * int * int =
  match s with
  | Zero -> (0, 0, 0, 0)
  | RightAngle -> (1, 0, 0, 0)
  | Length (a, b) -> (2, a, b, 0)
  | Angle (a, b, c) -> (3, a, b, c)
  | Area (a, b, c) -> (4, a, b, c)
  | Bvar id -> (5, id, 0, 0)
