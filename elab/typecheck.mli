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

(** [whnf e tm] computes the weak head normal form of `tm` with respect to the context
    `e`, recursing into known metavariable solutions and definitions. *)
val whnf : Types.ctx -> term -> term

(** [infertype ctx lctx tm] returns the inferred type of term [tm] in context [ctx].
    Refers to [ctx] for environment entries and [lctx] for bound variables. All holes in
    [tm] must have a relevant entry in [env.metas]. *)
val infertype : ?depth:int -> Types.ctx -> Types.local_ctx -> term -> term

(** [create_metas ctx tm ids] initializes the [ctx.metas] table with the hole ids present
    in [tm]. [ids] is the initial list of bids in scope. *)
val create_metas : Types.ctx -> term -> int list -> unit

(** [replace_metas ctx tm] replaces the metavariables in [tm] with their solved instances.
*)
val replace_metas : Types.ctx -> term -> term

(** [unify ctx ?lctx t1 tbl1 t2 tbl2] attempts to unify terms [t1] and [t2] (trying to
    make them definitionally equal by solving metavariables in each). Metavariable
    solutions are stored by mutating [ctx.metas]. Pass empty hashtables for [tbl1] and
    [tbl2]. If [t1] and [t2] do not contain any holes (after [unify] returns and after
    recursively replacing their solutions), [unify] returns successfully (i.e. does not
    raise ElabError) if and only if [t1] and [t2] are definitionally equal. Otherwise, if
    [t1] or [t2] contain holes after [unify] returns successfully, [unify] was unable to
    determine whether [t1] and [t2] could be made definitionally equal (e.g. because it
    would require higher order unification). If [unify] raises an error in any case, then
    [t1] and [t2] cannot be made definitionally equal. [?lctx] does not affect the
    functionality of the unification, but it will be passed to raised errors for better
    error messages. *)
val unify :
  ?depth:int ->
  Types.ctx ->
  ?lctx:Types.local_ctx ->
  term ->
  (int, int) Hashtbl.t ->
  term ->
  (int, int) Hashtbl.t ->
  unit
