(** Top-level elaborator API. *)

val create : unit -> Types.ctx
(** Create an empty elaboration context. *)

val create_with_env_path : string -> Types.ctx
(** [create_with_env_path path] creates an elaboration context pre-populated by
    type-checking and adding the declarations in the file at [path]. *)

val create_with_env : unit -> Types.ctx
(** [create_with_env ()] creates an elaboration context using the default environment file
    at ["elab/env.txt"]. *)

val parse_term : string -> Term.term
(** [parse_term s] parses a single term from the string [s]. *)

val parse_decls : string -> Decl.declaration list
(** [parse_decls filename] parses all declarations from the file [filename]. Raises
    [Error.ElabError] with a [ParseError] payload on failure. *)

val process_decl : Types.ctx -> Decl.declaration -> unit
(** [process_decl env decl] type-checks and adds [decl] to [env]. Raises [Error.ElabError]
    on type errors. *)

val process_file : Types.ctx -> string -> unit
(** [process_file env filename] parses and processes all declarations in [filename],
    adding them to [env]. *)

val list_axioms : Types.ctx -> string -> string list
(** [list_axioms env name] returns the list of axiom names that the theorem [name]
    transitively depends on. Raises [Failure] if [name] is not found or is itself an
    axiom. *)
