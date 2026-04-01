open Term
open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

(** A tactic is a function from proof state to tactic result. *)
type tactic = proof_state -> tactic_result

(* ------------------------------------------------------------------ *)
(* Tactic combinators                                                   *)
(* ------------------------------------------------------------------ *)

(** [seq t1 t2] applies [t1]; on success applies [t2] to the new state.
    Propagates the first failure without running [t2]. *)
val seq : tactic -> tactic -> tactic

(** [try_tac t] attempts [t]; if [t] fails, returns the original state
    unchanged.  Never fails. *)
val try_tac : tactic -> tactic

(** [repeat t] applies [t] until it fails, returning the last successful
    state.  Never fails. *)
val repeat : tactic -> tactic

(** Sequencing operator — alias for [seq]. *)
val ( >> ) : tactic -> tactic -> tactic

(* ------------------------------------------------------------------ *)
(* Core proof tactics                                                   *)
(* ------------------------------------------------------------------ *)

(** [reflexivity st] closes an [Eq A lhs rhs] goal when [lhs] and [rhs]
    are definitionally equal.  Proof term: [@refl A lhs]. *)
val reflexivity : proof_state -> tactic_result

(** [exact tm st] closes the current goal if [tm]'s inferred type is
    definitionally equal to the goal type.  Returns [Failure] if the types
    don't match, [tm] is ill-typed, or no goals remain. *)
val exact : term -> proof_state -> tactic_result

(** [apply name st] looks up [name] as a hypothesis or global lemma and
    attempts to close the current goal.
    - If [name : A → B] and the conclusion [B] equals the goal, closes the
      goal with proof [name ?premise] and opens a new subgoal for [A].
    - If the type directly matches the goal (no arrow), behaves like [exact].
    Hypotheses shadow globals with the same name. *)
val apply : string -> proof_state -> tactic_result

(** [sorry st] closes any goal with a logically unsound placeholder proof.
    Lazily registers [sorry_ax : (A : Prop) → A] as an axiom on first use.
    Emits a warning to stderr.  Use only during development. *)
val sorry : proof_state -> tactic_result

(** [intro name st] introduces the premise of an implication into the local
    context.  Precondition: current goal (after beta-normalisation) has shape
    [A → B].  Opens a new goal [name : A ⊢ B] and closes the current one
    with proof [fun (name : A) => ?body]. *)
val intro : string -> proof_state -> tactic_result

(** [intros names] applies [intro] for each name in order.  [intros []] is
    the identity.  Fails if any [intro] in the chain fails. *)
val intros : string list -> tactic

(** [have name ty st] introduces an intermediate lemma [name : ty].
    Replaces the current goal [G] with two subgoals in order:
      1. [ctx ⊢ ty]               — prove the intermediate claim
      2. [ctx ⊢ (name : ty) → G]  — prove the continuation
    Use [intro name] on the second subgoal to bring [name] into scope. *)
val have : string -> term -> tactic
