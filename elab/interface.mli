(** Top-level elaborator API. *)

(** [parse_term s] parses a single term from the string [s]. *)
val parse_term : string -> Term.term

(** [create ()] creates an empty elaboration context. *)
val create : unit -> Types.ctx

(** [process_file env filename] parses and processes all statements in [filename], adding
    them to [env]. *)
val process_file : Types.ctx -> string -> unit

(** [process_env env] populates [env] with the axioms from the default environment file at
    ["elab/env.ncg"]. *)
val process_env : Types.ctx -> unit
