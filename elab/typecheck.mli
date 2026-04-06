open Term

(** Type-checking and elaboration of terms and declarations.

    Implements bidirectional type-checking with pattern-unification–based hole inference.
    Holes written by the user as [_] are automatically filled in based on context. Solved
    terms are then verified by the trusted kernel before being committed to the
    environment.

    These functions may raise [Error.ElabError] on failure. *)

(** [process_decl ctx decl] type-checks and adds a single declaration to the elaboration
    context. *)
val process_decl : Types.ctx -> Statement.declaration -> unit

(** [elaborate ctx tm ty] elaborates term [tm] in context [ctx] with an optional expected
    type [ty]. Returns a filled term with type [ty], or raises [Error.ElabError]. *)
val elaborate : Types.ctx -> term -> term option -> term

(** [infertype ctx tm] returns the inferred type of term [tm] in context [ctx]. [tm] must
    be elaborated first. *)
val infertype : ?depth:int -> Types.ctx -> term -> term

val unify : ?depth:int -> Types.ctx -> term -> (int, int) Hashtbl.t ->
    term -> (int, int) Hashtbl.t -> unit