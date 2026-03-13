(** Beta-reduction for elaboration-level terms. *)

(** [reduce ctx tm] fully beta-reduces [tm], substituting solved metavariables. *)
val reduce : Types.ctx -> Term.term -> Term.term
