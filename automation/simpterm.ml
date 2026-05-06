(** it's kinda cumbersome to work with Elab.Terms with OCaml syntax since they're records.
    we define simpterm which is just term without location information making it easier to
    pattern match and stuff when we dont care about location information *)

type term =
  | Name of string
  | Bvar of int
  | Hole of int
  | Fun of string option * int * term * term
  | Arrow of string option * int * term * term
  | App of term * term
  | Sort of int

let rec to_simpterm (tm : Elab.Term.term) : term =
  let open Elab.Term in
  match tm.inner with
  | Name x -> Name x
  | Bvar idx -> Bvar idx
  | Hole idx -> Hole idx
  | Fun (x, bid, ty, body) -> Fun (x, bid, to_simpterm ty, to_simpterm body)
  | Arrow (x, bid, ty_arg, ty_ret) ->
      Arrow (x, bid, to_simpterm ty_arg, to_simpterm ty_ret)
  | App (f, arg) -> App (to_simpterm f, to_simpterm arg)
  | Sort n -> Sort n

let rec from_simpterm (st : term) : Elab.Term.term =
  let open Elab.Term in
  match st with
  | Name x -> { inner = Name x; loc = Elab.Term.dummy_range }
  | Bvar idx -> { inner = Bvar idx; loc = Elab.Term.dummy_range }
  | Hole idx -> { inner = Hole idx; loc = Elab.Term.dummy_range }
  | Fun (x, bid, ty, body) ->
      {
        inner = Fun (x, bid, from_simpterm ty, from_simpterm body);
        loc = Elab.Term.dummy_range;
      }
  | Arrow (x, bid, ty_arg, ty_ret) ->
      {
        inner = Arrow (x, bid, from_simpterm ty_arg, from_simpterm ty_ret);
        loc = Elab.Term.dummy_range;
      }
  | App (f, arg) ->
      { inner = App (from_simpterm f, from_simpterm arg); loc = Elab.Term.dummy_range }
  | Sort n -> { inner = Sort n; loc = Elab.Term.dummy_range }

let apps (f : term) (args : term list) : term =
  List.fold_left (fun acc arg -> App (acc, arg)) f args
