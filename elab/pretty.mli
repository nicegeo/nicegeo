(** Pretty-printing functions for elaboration-level terms. *)
open Term

(** [term_to_string ctx t] converts the elaboration term [t] to a human-readable string,
    consulting [ctx] for binder names, local-context names, and meta solutions. *)
val term_to_string : Types.ctx -> Term.term -> string

(** [pp_loc loc] formats a file range as a string, e.g. proof.txt:334:8-49 *)
val pp_loc : range -> string

(** [reduce ctx t] beta-reduces the term [t] in the context [ctx]. Ideally this is in a
    different module, it can't be in typecheck.ml because circular dependency *)
val reduce : Types.ctx -> term -> term
