(** Pretty-printing functions for elaboration-level terms. *)

val term_to_string : Types.ctx -> Term.term -> string
(** [term_to_string ctx t] converts the elaboration term [t] to a human-readable string,
    consulting [ctx] for binder names, local-context names, and meta solutions. *)

val decl_to_string : Types.ctx -> Decl.declaration -> string
(** [decl_to_string ctx d] formats a declaration as a string, e.g. ["Axiom name : ty"] or
    ["Theorem name : ty := proof"]. *)
