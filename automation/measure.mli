(** Measure representation and normalization. Measures are geometric quantities that can
    be added and compared. This module provides canonical ordering and normalization for
    measures. *)

(** Atomic measure components (summands) *)
type summand =
  | Zero
  | RightAngle
  | Length of int * int
  | Angle of int * int * int
  | Area of int * int * int
  | Bvar of int

(** A normalized measure as a list of summands with proof of equivalence *)
type measure = {
  summands : summand list;
  original : Simpterm.term;
  proof : Simpterm.term;  (** proof that summands_to_term summands = original *)
}

(** Convert an Elab.Term to a summand if it represents one *)
val to_summand : Elab.Term.term -> summand option

(** Convert a summand back to a simplified term *)
val summand_to_term : summand -> Simpterm.term

(** Convert a list of summands to a simplified term (represented as nested Adds) *)
val summands_to_term : summand list -> Simpterm.term

(** Convert a measure to an Elab.Term *)
val measure_to_term : measure -> Elab.Term.term

(** Parse a simplified term into a measure *)
val to_measure : Simpterm.term -> measure option

(** Create a measure from a list of summands *)
val measure_of_summands : summand list -> measure

(** Rewrite the first i summands of a measure *)
val congr : measure -> int -> summand list -> Simpterm.term -> measure

(** Rewrite the i-th summand of a measure *)
val rewrite_i : measure -> int -> summand -> Simpterm.term -> measure

(** Normalize individual summands *)
val normalize_summand : measure -> int -> measure

(** Normalize all summands *)
val normalize_summands : measure -> measure

(** Swap adjacent summands in a measure *)
val swap_adjacent : measure -> int -> measure

(** Sort summands *)
val sort : measure -> measure

(** Cancel zero terms *)
val cancel_zeros : measure -> measure

(** Fully normalize a measure *)
val normalize_measure : measure -> measure

(** Generate a proof of equality between two summand lists after normalization *)
val normalized_rfl : summand list -> summand list -> Simpterm.term

(** Generate a reflexivity proof for a term *)
val refl : Simpterm.term -> Simpterm.term

(** Generate a symmetric proof *)
val proof_symm : measure -> Simpterm.term
