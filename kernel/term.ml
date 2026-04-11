type term =
  | Const of string
  | Bvar of int
  | Fvar of string
  | Lam of term * term
  | Forall of term * term
  | App of term * term
  | Sort of int

(* Maps constants to their types and definitions. *)
type environment = {
  types : (string, term) Hashtbl.t;
  defs : (string, term) Hashtbl.t;
}

(* Maps free variable names to their types *)
type localcontext = (string, term) Hashtbl.t
