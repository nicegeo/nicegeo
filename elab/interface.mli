(** Top-level elaborator API. *)

(** [parse_term s] parses a single term from the string [s]. *)
val parse_term : string -> Term.term

(** [create ()] creates an empty elaboration context. *)
val create : unit -> Types.ctx

(** [get_all_statements filename] returns all statements from the file [filename],
    including those imported. The output will not contain any import statements. May raise
    [Error.ImportNotAtTop]. *)
val get_all_statements : string -> Statement.statement list

(** [process_statement env stmt] processes the statement [stmt] in the context [env].

    For a declaration, it typechecks it and then adds it to the environment.
    For a directive, it executes it and prints the result to stdout.
    For an import, it throws an error.
*)
val process_statement : Types.ctx -> Statement.statement -> unit

(** [process_file env filename] parses and processes all statements in [filename], adding
    them to [env]. *)
val process_file : Types.ctx -> string -> unit

(** [process_env env] populates [env] with the axioms from the default environment file at
    ["elab/env.ncg"]. *)
val process_env : Types.ctx -> unit
