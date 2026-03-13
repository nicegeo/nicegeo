(** Top-level elaborator API. *)

(** [parse_term s] parses a single term from the string [s]. *)
val parse_term : string -> Term.term

(** [create ()] creates an empty elaboration context. *)
val create : unit -> Types.ctx

(** [process_file env filename] parses and processes all statements in [filename], adding
    them to [env]. *)
val process_file : Types.ctx -> string -> unit

(** [process_env env] populates [env] with the axioms from the default environment file at
    ["elab/env.txt"]. *)
val process_env : Types.ctx -> unit

(** [list_axioms env name] returns the list of axiom names that the theorem [name]
    transitively depends on. Raises [Failure] if [name] is not found or is itself an
    axiom. *)
val list_axioms : Types.ctx -> string -> string list
