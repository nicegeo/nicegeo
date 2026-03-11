(** Types for the elaboration context. *)

open Term

(** A metavariable (hole) to be solved during elaboration. *)
type metavar = {
  ty : term option;  (** Expected type of the hole, if already known. *)
  vartypes : term list;
      (** Types of the free variables whose values the solution may depend on, in order
          (later entries may contain [Bvar]s referring to earlier ones). *)
  sol : term option;  (** Solution term once found; must be closed. *)
}

(** Data associated with each entry in the environment. *)
type enventry_data =
  | Theorem of string list
      (** [Theorem(axioms)] describes the axioms a theorem depends on. *)
  | Axiom  (** [Axiom] represents an axiom with no additional data. *)
  | Primitive
      (** [Primitive] represents a foundational declaration (type, relation, operation, or
          constant).*)

(** An entry in the elaboration environment. *)
type enventry = {
  name : string;
  ty : term;
  data : enventry_data;
}

(** Elaboration context. *)
type ctx = {
  env : (string, enventry) Hashtbl.t;
      (** Elaboration-level environment mapping defined names to their entries. *)
  kenv : Kernel.Term.environment;
      (** Kernel-level environment, kept in sync with [env]. *)
  metas : (int, metavar) Hashtbl.t;
      (** Mapping from hole ids to their metavariable records. *)
  lctx : (int, string option * term) Hashtbl.t;
      (** Local context mapping free-variable ids to their optional name and type. *)
}
