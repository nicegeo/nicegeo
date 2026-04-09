open Term
open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

type tactic = proof_state -> tactic_result

(** A registry mapping tactic names to their implementations. *)
val tactics : (string, term list -> tactic) Hashtbl.t

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
end
