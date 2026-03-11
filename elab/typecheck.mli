open Term

(** Type-checking and elaboration of declarations.

    Implements bidirectional type-checking with pattern-unification–based hole inference.
    Holes written by the user as [_] are replaced by metavariable spines, constraints are
    gathered during type-checking, and pattern unification fills in solutions. Solved
    terms are then verified by the trusted kernel before being committed to the
    environment. *)

(** [process_decl ctx decl] type-checks and adds a single declaration to the elaboration
    context. Raises [Error.ElabError] on any error. *)
val process_decl : Types.ctx -> Decl.declaration -> unit

val hole_to_meta : Types.ctx -> term list -> term -> term
val infertype : Types.ctx -> term -> term
val replace_metas : Types.ctx -> term -> term
val check_is_type : Types.ctx -> term -> unit
val checktype : Types.ctx -> term -> term -> unit
