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

(** [apply term st] attempts to solve the current goal by applying [term], opening
    subgoals for the remaining arguments (if any). *)
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

(** [split st] decomposes a goal of the form [And A B] into two subgoals [A] and [B],
    using [And.intro] as the proof skeleton. Fails if the goal is not a conjunction.
    (Normalizes, but does not do unification) *)
val split : proof_state -> tactic_result

(** [exists a] takes in a term [a] of type [A], and constructs a new goal [p a], where the
    old goal had form [Exists A p]. The motive [p] is inferred from the goal and the type
    of the argument [a]. *)
val exists : term -> proof_state -> tactic_result

(** * Given a term whose type unifies with [Exists A p], infer [A] and [p], * and
    introduce new hypotheses representing [a : A] and [h : p a]. * Update the proof term
    appropriately. *)
val choose : string * string -> term -> proof_state -> tactic_result

(** The [left] tactic checks that the goal is of the form Or A B, and then changes the
    goal type to A, creating a proof term using [Or.inl] *)
val left : proof_state -> tactic_result

(** The [right] tactic checks that the goal is of the form Or A B, and then changes the
    goal type to B, creating a proof term using [Or.inr] *)
val right : proof_state -> tactic_result

(** The [distinct_points] tactic takes a [distinct_from] proof as an argument, and from
    it proves an inequality between points and adds it to the hypotheses, asking
    for the [List.mem] proof obligation for now (future versions will probably
    try to prove this automatically when possible). *)
val distinct_points : string -> term -> proof_state -> tactic_result

val register : unit -> unit
