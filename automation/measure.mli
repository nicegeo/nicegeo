(** Measure representation and normalization. This module provides canonical ordering and
    normalization for measures. Normalized measures have additions fully left-associated,
    e.g. ((a + b) + c) + d, sorted by a canonical ordering on summands, and Zeros
    cancelled. *)

(** Atomic measure components (summands), identified and sorted by default OCaml
    lexicographic ordering. int components define Bvar indices of the corresponding
    [Point]s. Lengths are normalized to have the smaller Bvar index first (angle_symm and
    area perm normalization not implemented yet). Sums are generally internally
    represented as a nonempty [summand list] (0 is [[Zero]]), which corresponds to the
    unique term defined by [summands_to_term]. *)
type summand =
  | Zero
  | RightAngle
  | Length of int * int
  | Angle of int * int * int
  | Area of int * int * int
  | Bvar of int

(** A normalized measure as a list of summands with proof of equivalence to an original
    term *)
type measure = {
  summands : summand list;
  original : Simpterm.term;
  proof : Simpterm.term;  (** proof that summands_to_term summands = original *)
}

(** Convert an Elab.Term to a summand if it represents one *)
val to_summand : Elab.Term.term -> summand option

(** Convert a summand to its corresponding term *)
val summand_to_term : summand -> Simpterm.term

(** Convert a list of summands to the term it represents *)
val summands_to_term : summand list -> Simpterm.term

(** Simpterm.from_simpterm (summands_to_term m.summands) *)
val measure_to_term : measure -> Elab.Term.term

(** Parse a simplified term into a measure. This involves left-associating all Adds, so in
    the returned m, m.original is set to the passed in term and an appropriate m.proof is
    filled in. *)
val to_measure : Simpterm.term -> measure option

(** Create a measure from a list of summands, returned m.original is set to the passed in
    term *)
val measure_of_summands : summand list -> measure

(** Normalize all individual summands *)
val normalize_summands : measure -> measure

(** Sort summands in a measure *)
val sort : measure -> measure

(** Cancel zero terms in a measure. Measure must be sorted first (so that the Zeros are in
    the front) *)
val cancel_zeros : measure -> measure

(** Fully normalize a measure (normalizes and sorts summands and cancels zeros) *)
val normalize_measure : measure -> measure

(** [normalized_rfl a b] Generate a proof of [a = b], assuming they have equal normal
    forms *)
val normalized_rfl : summand list -> summand list -> Simpterm.term

(** Generates a proof [original = summands_to_term m.summands] *)
val proof_symm : measure -> Simpterm.term
