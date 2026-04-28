(** Tactic for normalizing measures in goals. Applies measure normalization to the current
    goal. *)

(** Normalize measures in the current goal *)
val measure_norm : Elab.Proofstate.proof_state -> Elab.Tactic.tactic_result
