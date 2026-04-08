open Term

type tactic = {
  name : string;
  args : term list;
  loc : range;
}

type theorem_body =
  | Proof of tactic list
  | DefEq of term

type decl_type =
  | Theorem of theorem_body
  | Axiom
  | Def of term

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
  | Opaque of string * range

type import = { filename : string }

type statement =
  | Declaration of declaration
  | Directive of directive
  | Import of import
