(** Declaration type. A file consists of a list of declarations. *)

open Term

(** The body of a declaration: either a proof term or an axiom. *)
type decl_type =
  | Theorem of term  (** A theorem with its proof term. *)
  | Axiom  (** An axiom. *)

(** A parsed declaration (axiom or theorem). *)
type declaration = {
  name : string;
  name_loc : range;
  ty : term;
  kind : decl_type;
}
