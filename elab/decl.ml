open Term

type declaration =
  | Theorem of string * term * term
  | Axiom of string * term

let decl_name (decl: declaration) : string =
  match decl with
  | Theorem (name, _, _) -> name
  | Axiom (name, _) -> name