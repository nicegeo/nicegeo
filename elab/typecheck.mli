open Term

(** Type-checking and elaboration of declarations.

    Implements bidirectional type-checking with pattern-unification–based hole inference.
    Holes written by the user as [_] are replaced by metavariable spines, constraints are
    gathered during type-checking, and pattern unification fills in solutions. Solved
    terms are then verified by the trusted kernel before being committed to the
    environment.

    These functions may raise [Error.ElabError] on failure. *)

(** [process_decl ctx decl] type-checks and adds a single declaration to the elaboration
    context. *)
val process_decl : Types.ctx -> Statement.declaration -> unit

(** [hole_to_meta ctx stack tm] returns tm unchanged except for replacing holes with
    metavariable spines.

    `stack` is the types of all of the bound variables introduced outside of the term,
    where the first element is the innermost definition (i.e. what `Bvar 0` would
    correspond to) *)
val hole_to_meta : Types.ctx -> term list -> term -> term

(** [infertype ctx tm] returns the inferred type of term [tm] in context [ctx], filling in
    metavariables. *)
val infertype : Types.ctx -> term -> term

(** [replace_metas ctx tm] replaces all holes in [tm] with their solutions in context
    [ctx]. *)
val replace_metas : Types.ctx -> term -> term

(** [check_is_type ctx tm] checks that [tm] is a type in context [ctx], filling in
    metavariables. *)
val check_is_type : Types.ctx -> term -> unit

(** [checktype ctx tm ty] checks that [tm] has type [ty] in context [ctx], filling in
    metavariables. *)
val checktype : Types.ctx -> term -> term -> unit
