type term =
  | Name of string
  | Hole
  | Fun of string * term * term  (* argument name, type, body *)
  | Arrow of string * term * term  (* argument name, type, return type *)
  | App of term * term
  | Sort of int

