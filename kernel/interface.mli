(** This is the core entry point of the kernel, allowing the addition of type-checked
    theorems and axioms into a kernel environment. *)
open Term

(** [create ()] Creates a new, empty kernel environment. *)
val create : unit -> environment

(** [add_theorem env name ty tm] Type-checks and adds a theorem to the environment,
    throwing a TypeError on failure. *)
val add_theorem : environment -> string -> term -> term -> unit

(** [add_axiom env name ty] Type-checks and adds an axiom to the environment, throwing a
    TypeError on failure. *)
val add_axiom : environment -> string -> term -> unit

(** [add_definition env name ty tm] Type-checks and adds a definition to the environment,
    throwing a TypeError on failure. *)
val add_definition : environment -> string -> term -> term -> unit
