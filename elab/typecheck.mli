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

(** [elaborate ctx tm ty] elaborates term [tm] with an optional expected type [ty]. Refers
    to [ctx] for environment entries. Returns a filled term with type [ty], or raises
    [Error.ElabError]. *)
val elaborate : Types.ctx -> term -> term option -> term

(** [infertype ctx lctx tm] returns the inferred type of term [tm] in context [ctx]. Refers to [ctx] for environment entries and [lctx] for bound variables. All holes in [tm] must
    have a relevant entry in [env.metas]. *)
val infertype : ?depth:int -> Types.ctx -> Types.local_ctx -> term -> term

(** [create_metas ctx tm ids] initializes the [ctx.metas] table with the hole ids present
    in [tm]. [ids] is the initial list of bids in scope. *)
val create_metas : Types.ctx -> term -> int list -> unit

(** [replace_metas ctx tm] replaces the metavariables in [tm] with their solved instances.
*)
val replace_metas : Types.ctx -> term -> term

val unify :
  ?depth:int ->
  Types.ctx ->
  term ->
  (int, int) Hashtbl.t ->
  term ->
  (int, int) Hashtbl.t ->
  unit
