(** Fourier-Motzkin elimination for measure constraints. Decides (in)equalities on
    Measures using Fourier-Motzkin elimination algorithm. *)

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

(** Multiply a term n times (n * a = a + a + ... + a) *)
val times : int -> term -> term

(** Generate a proof that n * a rel n * b *)
val order_mul : term -> term -> int -> term

(** Generate a proof that n * a < n * b *)
val lt_mul : int -> term

(** Generate a proof that n * a <= n * b *)
val le_mul : int -> term

(** Generate a proof that n * a = n * b *)
val eq_mul : int -> term

(** Convert relation to term representation *)
val relation_to_term : relation -> term

(** Get the type of a constraint as a term *)
val constrain_ty : constrain -> term

(** Rewrite the left-hand side of a constraint *)
val rewrite_lhs : constrain -> summand list -> term -> constrain

(** Rewrite the right-hand side of a constraint *)
val rewrite_rhs : constrain -> summand list -> term -> constrain

(** Sort both sides of a constraint *)
val sort_sides : constrain -> constrain

(** Normalize both sides of a constraint *)
val normalize_sides : constrain -> constrain

(** Cancel common terms from both sides *)
val cancel_ij : constrain -> int -> int -> constrain

(** Simplify a constraint by canceling common terms *)
val simp_constrain : constrain -> constrain

(** Add a summand to both sides of a constraint *)
val add_one_both_sides : constrain -> summand -> constrain

(** Add a list of summands to both sides *)
val add_both_sides : constrain -> summand list -> constrain

(** Extract coefficient of a summand in a list *)
val coefficient : summand list -> summand -> int

(** Compute GCD *)
val gcd : int -> int -> int

(** Compute LCM *)
val lcm : int -> int -> int

(** Multiply a constraint by a scalar *)
val mult_constrain : constrain -> int -> constrain

(** Find leveled sums *)
val level_sums : summand list -> summand list -> summand list * summand list

(** Match sides to prepare for cancellation *)
val match_sides_to_cancel :
  constrain -> bool -> constrain -> bool -> summand -> constrain * constrain

(** Eliminate an atom from constraints using an equality *)
val elim_eq : constrain list -> int -> summand -> constrain list

(** Eliminate all occurrences of an atom *)
val elim_atom : constrain list -> summand -> constrain list

(** Preprocess a hypothesis term to extract relation, lhs, rhs, and proof *)
val preprocess_hyp : term -> term -> (relation * term * term * term) option

(** Create a constraint from a hypothesis type and proof *)
val create_constrain : term -> term -> constrain option

(** Try to prove false using Fourier-Motzkin elimination *)
val try_prove_false :
  Elab.Types.ctx -> Elab.Types.local_ctx -> constrain list -> term option
