# Proof Status Summary

**Main goal:** `square_of_len` (Euclid I.46) ✓

## Final status
- `square_of_len` is fully proved.
- `dune exec nicegeo proof.ncg` returns `Valid proofs!`
- `dune exec nicegeo proof.ncg | grep sorry` does not list `sorry`.

## Completed dependency path to Prop. 46
- Prop. 10 `bisect_segment` ✓
- Prop. 11 `perpendicular_of_online'`, `perpendicular_of_online''` ✓
- Prop. 13 `two_right_of_flat_angle`, `right_of_online_right` ✓
- Prop. 15 `vertical_angle`, `vertical_angle'` ✓
- Prop. 16 `internal_lt_external`, `internal_lt_external'` ✓
- Prop. 18 `ang_lt_of_len_lt` ✓
- Prop. 19 `len_lt_of_ang_lt` ✓
- Prop. 20 `len_lt_of_tri`, `len_lt_of_tri'` ✓
- Prop. 22 `triangle_of_ineq` ✓
- Prop. 23 `angle_copy`, `angle_copy'` ✓
- Prop. 27 `para_of_ang_eq` ✓
- Prop. 29 `alternate_interior_angle`, `co_interior_angles` ✓
- Prop. 30 `para_trans` ✓
- Prop. 31 `para_of_offline` ✓
- Prop. 34 `len_ang_arelen_ang_area_eq_of_parallelogram` ✓
- Prop. 34 `len_eq_of_parallelogram` ✓
- Prop. 34 `len_eq_of_parallelogram'` ✓
- Prop. 34 `len_eq_of_parallelogram''` ✓
- Prop. 46 helper `lines_inter_of_parallel_through_transversal` ✓
- Prop. 46 helper `lines_inter_of_crossing_parallels` ✓
- Prop. 46 helper `same_side_of_points_on_parallel` ✓

## Proof shape of Prop. 46
- Build the base line through `a,b`.
- Erect a perpendicular at `a`.
- Place `d` on that perpendicular with `ad = ab`.
- Draw through `d` a line parallel to `ab`, and through `b` a line parallel to `ad`.
- Let `e` be their intersection.
- Show `a d e b` is a parallelogram.
- Use Prop. 34 to get opposite-side equalities.
- Use Prop. 29 and Prop. 13 to show all angles are right angles.
- Package the square as `square a b e d`.

## Validation used
- `dune exec nicegeo proof.ncg`
- `python3 deps.py square_of_len`
- `#print axioms square_of_len`

## Note
- Some point-construction axioms in `synthetic/env.ncg` are stronger-looking than the corresponding System E presentation, but Prop. 46 is now proved on the original `main` branch axiom file.
