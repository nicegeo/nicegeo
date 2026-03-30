(** Statement type. A file consists of a list of statements, which are either declarations
    or directives. *)

open Term

(** The body of a declaration: either a proof term or definition body or an axiom. *)
type decl_type =
  | Theorem of term
      (** [Theorem(term)] is the type of theorems with proof [term]. *)
  | Axiom  (** [Axiom] is the type of axioms. *)
  | Def of term  (** [Def(term)] is the type of definitions with body [term]. *)

(** A parsed declaration (axiom, theorem, or definition). *)
type declaration = {
  name : string;
  name_loc : range;
  ty : term;
  kind : decl_type;
}

(** A parsed directive (e.g., #print axioms, #infer). *)
type directive =
  | PrintAxioms of string * range
      (** [PrintAxioms(name, loc)] corresponds to #print axioms name. *)
  | Infer of term * range  (** [Infer(t, loc)] corresponds to #infer t. *)
  | Check of term * term * range  (** [Check(t, ty, loc)] corresponds to #check t : ty. *)
  | Reduce of term * range  (** [Reduce(t, loc)] corresponds to #reduce t. *)
  | Opaque of string * range  (** [Opaque(name, loc)] corresponds to #opaque name. *)

(** A parsed statement (either a declaration or a directive). *)
type statement =
  | Declaration of declaration
      (** [Declaration(decl)] is a parsed declaration, intended to be added to the
          environment. *)
  | Directive of directive
      (** [Directive(dir)] is a parsed directive, printing information to stdout. *)
