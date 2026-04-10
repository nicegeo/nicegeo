type term =
  | Const of string
  | Bvar of int
  | Fvar of string
  | Lam of term * term
  | Forall of term * term
  | App of term * term
  | Sort of int

(* Maps free variable names to their types *)
type localcontext = (string, term) Hashtbl.t
