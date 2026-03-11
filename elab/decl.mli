(** Declaration type. A file consists of a list of declarations. *)

open Term

(** The body of a declaration: either a proof term or an axiom. *)
type decl_type =
  | Theorem of term
      (** [Theorem(term)] is the type of theorems with definition [term]. *)
  | Axiom  (** [Axiom] is the type of axioms. *)

(** A parsed declaration (axiom or theorem). *)
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

type statement =
  | Declaration of declaration
  | Directive of directive
