(** Statement type. A file consists of a list of statements, which are either declarations
    or directives. *)

open Term

type tactic = {
  name : string;  (** The name of the tactic. *)
  args : term list;  (** The arguments passed to the tactic. *)
  loc : range;  (** The source location of the tactic (for error reporting). *)
}

type theorem_body =
  | Proof of tactic list
      (** [Proof(tactics)] represents a proof script, which is a sequence of tactics. *)
  | DefEq of term  (** [DefEq(term)] represents defining a theorem by a term. *)

(** The body of a declaration: either a proof or definition body or an axiom. *)
type decl_type =
  | Theorem of theorem_body
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

type import = { filename : string }

(** A parsed statement (either a declaration or a directive). *)
type statement =
  | Declaration of declaration
      (** [Declaration(decl)] is a parsed declaration, intended to be added to the
          environment. *)
  | Directive of directive
      (** [Directive(dir)] is a parsed directive, printing information to stdout. *)
  | Import of import
      (** [Import(import)] is a parsed import statement, intended to be processed by
          reading the specified file and elaborating its contents. *)
