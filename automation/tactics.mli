open Elab.Term
open Elab.Proofstate
open Elab.Tactic

val reflexivity : proof_state -> tactic_result

(** [sorry st] closes any goal with a placeholder proof. Logically unsound — will not pass
    kernel checking. Use only during development to defer proof obligations. *)
val sorry : proof_state -> tactic_result

(** [exact tm st] closes the current goal if [tm]'s inferred type is definitionally equal
    to the goal type. Returns [Failure] if the types don't match, the term is ill-typed,
    or no goals remain. *)
val exact : term -> proof_state -> tactic_result

(** [apply term st] if [term]'s type is [A -> B] and [B] matches the goal, closes the goal
    and opens a new subgoal for [A]. *)
val apply : term -> proof_state -> tactic_result

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

(** [exists a] takes in a term [a] of type [A], and constructs a new goal [p a], where the
    old goal had form [Exists A p]. The motive [p] is inferred from the goal and the type
    of the argument [a]. *)
val exists : term -> proof_state -> tactic_result

(** * Given a term whose type unifies with [Exists A p], infer [A] and [p], * and
    introduce new hypotheses representing [a : A] and [h : p a]. * Update the proof term
    appropriately. *)
val choose : string * string -> term -> proof_state -> tactic_result

val register : unit -> unit
