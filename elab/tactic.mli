open Term
open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

type tactic = proof_state -> tactic_result

(** A registry mapping tactic names to their implementations. *)
val tactics : (string, term list -> tactic) Hashtbl.t

type tactic_step_outcome =
  | Tactic_step_ok of proof_state
  | Tactic_step_unknown
  | Tactic_step_failed of string

(** [apply_tactic_step st tac] runs one parsed tactic if it is registered; otherwise
    [Tactic_step_unknown]. A registered tactic that returns [Failure] yields
    [Tactic_step_failed] (callers keep the pre-step proof state). *)
val apply_tactic_step : proof_state -> Statement.tactic -> tactic_step_outcome

(** [apply_first_k_tactics init tacs k] applies the first [k] tactics in order, stopping
    early if a step is unknown or fails (the proof state is then the last good state). *)
val apply_first_k_tactics : proof_state -> Statement.tactic list -> int -> proof_state

(** [run ctx tactics goal] runs a list of tactics in sequence, using the given context. It
    returns a hole, representing the proof to be solved. *)
val run : Types.ctx -> Statement.tactic list -> term -> term

(** [register_tactic name tac] registers a new tactic with the given name and
    implementation. *)
val register_tactic : string -> (term list -> tactic) -> unit

module Register : sig
  val nullary : tactic -> term list -> tactic
  val unary_term : (term -> tactic) -> term list -> tactic
  val unary_ident : (string -> tactic) -> term list -> tactic
  val variadic_term : (term list -> tactic) -> term list -> tactic
  val variadic_ident : (string list -> tactic) -> term list -> tactic
  val tactical : (tactic -> tactic) -> term list -> tactic
end
