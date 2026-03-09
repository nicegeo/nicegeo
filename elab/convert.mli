(** Conversion functions between elaboration-level and kernel-level terms. *)

(** Converts an elaboration-level term to a kernel-level term. The input term must not
    contain any holes ([Hole _]) or free variables ([Fvar _]). *)
val conv_to_kterm : Term.term -> Kernel.Term.term

(** Converts a kernel-level term to an elaboration-level term. *)
val conv_to_term : Kernel.Term.term -> Term.term
