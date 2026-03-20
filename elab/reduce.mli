(** Beta-reduction for elaboration-level terms. *)

(** [subst e tm pat replacement] substitutes all occurrences of [pat] (name/bvar) with
    [replacement] in [tm], recursing into known metavariable solutions. *)
val subst : Types.ctx -> Term.term -> Term.termkind -> Term.termkind -> Term.term

(** [reduce ctx tm] fully beta-reduces [tm], substituting solved metavariables. *)
val reduce : Types.ctx -> Term.term -> Term.term

(** [delta_reduce e tm full] delta-reduces [tm], substituting defined names with their
    definitions. [full] specifies whether definitions marked as opaque should be
    delta-reduced as well (for passing into the kernel). *)
val delta_reduce : Types.ctx -> Term.term -> bool -> Term.term
