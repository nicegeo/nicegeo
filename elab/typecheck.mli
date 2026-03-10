(** Type-checking and elaboration of declarations.

    Implements bidirectional type-checking with pattern-unification–based hole inference.
    Holes written by the user as [_] are replaced by metavariable spines, constraints are
    gathered during type-checking, and pattern unification fills in solutions. Solved
    terms are then verified by the trusted kernel before being committed to the
    environment. *)

(** Type-check and add a single declaration to the elaboration context. Raises
    [Error.ElabError] on any error. *)
val process_decl : Types.ctx -> Decl.declaration -> unit
