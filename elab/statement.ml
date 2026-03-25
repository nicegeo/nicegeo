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

type directive =
  | PrintAxioms of string * range
  | Infer of term * range
  | Check of term * term * range
  | Reduce of term * range

type import = {
  filename : string;
}

type statement =
  | Declaration of declaration
  | Directive of directive
  | Import of import
