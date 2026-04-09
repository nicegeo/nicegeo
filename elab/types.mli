(** Types for the elaboration context. *)

open Term

(** A metavariable (hole) to be solved during elaboration. *)
type metavar = {
  ty : term option;  (** Expected type of the hole, if already known. *)
  context : int list;
      (** list of binder ids that are in scope when the hole is defined *)
  sol : term option;  (** Solution term once found *)
}

(** Data associated with each entry in the environment. *)
type enventry_data =
  | Theorem of string list
      (** [Theorem(axioms)] describes the axioms a theorem depends on. *)
  | Axiom  (** [Axiom] represents an axiom with no additional data. *)
  | Def of string list * term * bool
      (** [Def(axioms, body, opaque)] describes a definition with body [body] and the
          axioms it depends on. [opaque] indicates whether the definition should be
          treated as "opaque". *)

(** An entry in the elaboration environment. *)
type enventry = {
  name : string;
  ty : term;
  data : enventry_data;
}

(** Local context entry. *)
type lctx_entry = {
  bid : int;
  name : string option;
  ty : term;
}

(** Local context used when typechecking. Logically a mapping from bids to their optional
    names and types. *)
type local_ctx = lctx_entry list

(** Elaboration context. *)
type ctx = {
  env : (string, enventry) Hashtbl.t;
      (** Elaboration-level environment mapping defined names to their entries. *)
  kenv : Kernel.Term.environment;
      (** Kernel-level environment, kept in sync with [env]. *)
  metas : (int, metavar) Hashtbl.t;
      (** Mapping from hole ids to their metavariable records. *)
}
