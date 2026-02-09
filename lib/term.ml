type term =
    | Const of string
    | Bvar of int
    | Fvar of string
    | Lam of term * term
    | Forall of term * term
    | App of term * term
    | Sort of int

(* Maps constants (and free variables) to their types *)
type environment = (string, term) Hashtbl.t

(* Stack of types for bound variables: head = type of Bvar 0 (innermost binder) *)
type localcontext = (string, term) Hashtbl.t