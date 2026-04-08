(** This is the core entry point of the kernel, allowing the addition of type-checked
    theorems and axioms into a kernel environment. *)
open Term

(** [add_theorem env name ty tm] Type-checks and adds a theorem to the environment,
    throwing a TypeError on failure. *)
val add_theorem : environment -> string -> term -> term -> unit

(** [add_axiom env name ty] Type-checks and adds an axiom to the environment, throwing a
    TypeError on failure. *)
val add_axiom : environment -> string -> term -> unit
