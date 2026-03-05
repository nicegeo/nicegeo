open Term

type decl_type =
  | Theorem of term
  | Axiom

type declaration = {
  name : string;
  name_loc : range;
  ty : term;
  kind : decl_type;
}
