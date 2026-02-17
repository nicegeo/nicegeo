open Term

type declaration =
  | Theorem of string * term * term
  | Axiom of string * term
