(** Pretty-printing functions for elaboration-level terms. *)
open Term

(** [term_to_string ctx t] converts the elaboration term [t] to a human-readable string,
    consulting [ctx] for binder names. *)
val term_to_string : Types.ctx -> Term.term -> string

(** [pp_loc loc] formats a file range as a string, e.g. proof.ncg:334:8-49 *)
val pp_loc : range -> string
