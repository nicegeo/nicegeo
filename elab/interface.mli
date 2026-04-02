(** Top-level elaborator API. *)

(** [parse_term s] parses a single term from the string [s]. *)
val parse_term : string -> Term.term

(** [create ()] creates an empty elaboration context. *)
val create : unit -> Types.ctx

(** [parse_statements filename] parses all statements from the file [filename]. *)
val parse_statements : string -> Statement.statement list

(** [process_statement env stmt] processes the statement [stmt] in the context [env]. *)
val process_statement : Types.ctx -> Statement.statement -> unit

(** [process_file env filename] parses and processes all statements in [filename], adding
    them to [env]. *)
val process_file : Types.ctx -> string -> unit

(** [process_env env] populates [env] with the axioms from the default environment file at
    ["elab/env.ncg"]. *)
val process_env : Types.ctx -> unit
