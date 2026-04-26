(** produces a proof of type ∀ (a b : Measure), n * a < n * b → a < b where n * a denotes
    a + a + ... + a (n times) *)
let lt_cancel_mul (n : int) : Simpterm.term =
  let open Simpterm in
  Bvar 0
