(** Decides (in)equalities on Measures using Fourier-Motzkin elimination algorithm. *)

open Simpterm
open Measure

(** Relation type for constraints *)
type relation =
  | Lt
  | Le
  | Eq

(** A measure constraint with a relation and proof *)
type constrain = {
  r : relation;
  lhs : summand list;
  rhs : summand list;
  proof : term;  (** proof of lhs (R) rhs *)
}

(** Get the proof type of a constraint as a term *)
val constrain_ty : constrain -> term

(** Simplify a constraint by canceling common terms *)
val simp_constrain : constrain -> constrain

(** Create a constraint from a hypothesis type and proof *)
val create_constrain : term -> term -> constrain option

val elim_eq : constrain list -> int -> summand -> constrain list

(** Try to prove false from a list of constraints using Fourier-Motzkin elimination *)
val try_prove_false :
  Elab.Types.ctx -> Elab.Types.local_ctx -> constrain list -> term option
