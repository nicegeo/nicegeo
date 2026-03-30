open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

val reflexivity : proof_state -> tactic_result

(** [sorry st] closes any goal with a placeholder proof.
    Logically unsound — will not pass kernel checking.
    Use only during development to defer proof obligations. *)
val sorry : proof_state -> tactic_result