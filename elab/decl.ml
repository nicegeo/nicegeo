open Term

type declaration =
  | Theorem of string * range * term * term
  | Axiom of string * range * term

let decl_name (decl: declaration) : string =
  match decl with
  | Theorem (name, _, _, _) -> name
  | Axiom (name, _, _) -> name