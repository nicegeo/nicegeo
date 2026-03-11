(** Pretty-printing functions for elaboration-level terms. *)
open Term

(** [term_to_string ctx t] converts the elaboration term [t] to a human-readable string,
    consulting [ctx] for binder names, local-context names, and meta solutions. *)
val term_to_string : Types.ctx -> Term.term -> string

(** [decl_to_string ctx d] formats a declaration as a string, e.g. ["Axiom name : ty"] or
    ["Theorem name : ty := proof"]. *)
val decl_to_string : Types.ctx -> Statement.declaration -> string

val pp_loc : range -> string
val reduce : Types.ctx -> term -> term
