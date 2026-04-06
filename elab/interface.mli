(** Top-level elaborator API. *)

(** [create ()] creates an empty elaboration context. *)
val create : unit -> Types.ctx

(** [create_with_env_path path] creates an elaboration context pre-populated by
    type-checking and adding the declarations in the file at [path]. *)
val create_with_env_path : string -> Types.ctx

(** [create_with_env ()] creates an elaboration context using the default environment file
    at ["synthetic/env.ncg"]. *)
val create_with_env : unit -> Types.ctx

(** [parse_term s] parses a single term from the string [s]. *)
val parse_term : string -> Term.term

(** [get_all_statements filename] returns all statements from the file [filename],
    including those imported. The output will not contain any import statements. May raise
    [Error.ImportNotAtTop]. *)
val get_all_statements : string -> Statement.statement list

(** [process_statement env stmt] processes the statement [stmt] in [env]. *)
val process_statement : Types.ctx -> Statement.statement -> unit

(** [process_file env filename] parses and processes all statements in [filename], adding
    them to [env]. *)
val process_file : Types.ctx -> string -> unit
