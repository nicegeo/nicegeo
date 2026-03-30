(** Conversion functions between elaboration-level and kernel-level terms. *)

(** [conv_to_kterm term] converts an elaboration-level term to a kernel-level term. The
    input term must not contain any holes ([Hole _]) and must be closed (any [Bvar idx]
    must correspond to an enclosing [Fun] or [Arrow] with the same id). *)
val conv_to_kterm : Term.term -> Kernel.Term.term
