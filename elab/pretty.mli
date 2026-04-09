(** Pretty-printing functions for elaboration-level terms. *)
open Term

(** [term_to_string ctx lctx t] converts the elaboration term [t] to a human-readable
    string, consulting [ctx] and local binders [lctx] for names. *)
val term_to_string : Types.ctx -> Types.local_ctx -> Term.term -> string

(** [pp_loc loc] formats a file range as a string, e.g. proof.ncg:334:8-49 *)
val pp_loc : range -> string

(** [decl_to_string ctx d] formats a declaration as a string, e.g. ["Axiom name : ty"] or
    ["Theorem name : ty := proof"]. *)
val decl_to_string : Types.ctx -> Statement.declaration -> string
