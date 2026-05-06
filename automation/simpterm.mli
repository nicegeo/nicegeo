(** Simplified term representation without location information. This makes it easier to
    pattern match and work with terms when location information is not needed. *)
type term =
  | Name of string
  | Bvar of int
  | Hole of int
  | Fun of string option * int * term * term
  | Arrow of string option * int * term * term
  | App of term * term
  | Sort of int

(** Convert an Elab term to a simplified term *)
val to_simpterm : Elab.Term.term -> term

(** Convert a simplified term back to an Elab term with dummy locations *)
val from_simpterm : term -> Elab.Term.term

(** Apply a function to a list of arguments *)
val apps : term -> term list -> term
