(** Pretty-printing functions for kernel-level terms. *)

(** [term_to_string_pretty ?names t] converts kernel term [t] to a string. [names] is the
    list of binder names in scope from innermost (index 0) outward. *)
val term_to_string_pretty : ?names:string list -> Kernel.Term.term -> string
