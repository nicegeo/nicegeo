open Term
open Proofstate
open Tactic

val reflexivity : proof_state -> tactic_result

(** [sorry st] closes any goal with a placeholder proof. Logically unsound — will not pass
    kernel checking. Use only during development to defer proof obligations. *)
val sorry : proof_state -> tactic_result

(** [exact tm st] closes the current goal if [tm]'s inferred type is definitionally equal
    to the goal type. Returns [Failure] if the types don't match, the term is ill-typed,
    or no goals remain. *)
val exact : term -> proof_state -> tactic_result

(** [apply name st] looks up [name] as a hypothesis or global lemma and attempts to close
    the current goal. If the lemma type is [A -> B] and [B] matches the goal, the goal is
    closed and a new subgoal for [A] is opened. If the type directly matches the goal (no
    arrow), it behaves like [exact]. *)
val apply : string -> proof_state -> tactic_result

(* sequences tactics *)
val seq : tactic -> tactic -> tactic

(* tries tactic. If succeeds then return new state, if fail then return original state*)
val try_tac : tactic -> tactic

(* repeat tactic application *)
val repeat : tactic -> tactic
val ( >> ) : tactic -> tactic -> tactic
val have : string -> term -> tactic
val intro : string -> tactic
val intros : string list -> tactic

(** [rewrite h] takes in a term [h] of type [lhs = rhs] and creates a new goal where all
    occurrences of [lhs] are replaced with [rhs] *)
val rewrite : term -> proof_state -> tactic_result

val register : unit -> unit
