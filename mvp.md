# MVP Roadmap: proof.ncg

**Ultimate goal:** `square_of_len` (Prop 46)
Run `python3 deps.py` for the full dependency graph.

---

## Prop 5 — Base angles of isosceles triangle ✓
**Milestone:** `angle_eq_of_iso` — `iso_tri a b c → Angle a b c = Angle a c b`
> ✓ PROVED (SSS on triangles (a,b,c) and (a,c,b))

---

## Prop 6 — Equal angles imply isosceles
**Milestone:** `eq_angles_implies_isoceles`
> `triangle a b c → Angle a b c = Angle a c b → Length a b = Length a c`
> TODO

---

## Prop 10 — Bisecting a segment ✓
**Milestone:** `bisect_segment`
> `a ≠ b → ∃ e, Between a e b ∧ Length a e = Length b e`
> ✓ PROVED

Helpers proved:
- `iseqtri_iseqtri_diffside_of_ne` ✓

---

## Prop 11 — Erecting a perpendicular ✓
**Milestone:** `perpendicular_of_online'` / `perpendicular_of_online''`
> Perpendicular at b on L, on same/opposite side as f
> ✓ PROVED

Helpers (all proved ✓):
- `length_eq_B_of_ne`: `a ≠ b → b ≠ c → ∃ d, Between a b d ∧ length b c = length b d`
- `iseqtri_sameside_of_ne`: `∃ c, ¬OnLine c L ∧ SameSide c d L ∧ eq_tri a b c`
- `angle_extension_of_B_B`: `B(a,b,c) ∧ B(a,b,d) → Angle e b d = Angle e b c`

---

## Prop 13 — Angles on a straight line sum to two right angles ✓
**Milestone:** `two_right_of_flat_angle` / `right_of_online_right`
> `Between a b c → ¬OnLine d L → Angle d b a + Angle d b c = 90 + 90`
> ✓ PROVED

Helpers (proved ✓):
- `online_of_sameside_inter`
- `angle_extension_of_sameside`
- `angle_add_of_sameside`
- `sum_two_right_from_splits`
- `not_sameside_of_sameside_sameside`
- `diffside_of_sameside_sameside`
- `offline_of_B_offline`
- `diffside_of_B_offline`
- `diffside_of_B_offline''`
- `sameside_of_B_diffside`
- `sameside_of_B_sameside_sameside`
- `two_right_of_flat_angle_same_side_case`
- `right_of_online_right`

---

## Prop 15 — Vertical angles ✓
**Milestone:** `vertical_angle` / `vertical_angle'`
> `Angle a b d = Angle c b e`
> ✓ PROVED

---

## Prop 16 — Exterior angle exceeds remote interior angles ✓
**Milestone:** `internal_lt_external` / `internal_lt_external'`
> `Between a b c → triangle a b d → Angle b d a < Angle d b c`
> ✓ PROVED

Helpers proved:
- `col_of_B` ✓
- `col_132_of_col` ✓

---

## Prop 18 — Larger side opposite larger angle
**Milestone:** `ang_lt_of_len_lt`
> `triangle a b c → length c a < length c b → angle c b a < angle c a b`
> TODO

---

## Prop 19 — Larger angle opposite larger side
**Milestone:** `len_lt_of_ang_lt`
> `triangle a b c → angle c b a < angle c a b → Length c a < Length c b`
> TODO

---

## Prop 20 — Triangle inequality
**Milestone:** `len_lt_of_tri`
> All three inequalities: each side < sum of the other two
> TODO

Helper:
- `len_lt_of_tri'`: `triangle a b c → Length a b < Length a c + Length b c` — TODO

---

## Prop 22 — Constructing a triangle from three lengths
**Milestone:** `triangle_of_ineq`
> Given lengths satisfying triangle inequality, construct point e on same side as f
> TODO

---

## Prop 23 — Copying an angle
**Milestone:** `angle_copy` / `angle_copy'`
> Copy angle ecd to vertex a on line L, same/opposite side as j
> TODO

---

## Prop 27 — Equal alternate interior angles imply parallel lines ✓
**Milestone:** `para_of_ang_eq`
> `Angle c b a = Angle b c d → para M N`
> ✓ PROVED

Helpers proved:
- `offline_of_online_inter` ✓

---

## Prop 29 — Parallel lines and transversals ✓
**Milestone:** `co_interior_angles`
> `para L M → ... → Angle a b c + Angle b c d = 90 + 90`
> ✓ PROVED

Additional:
- `no_lt_of_parallel_alternate` ✓
- `alternate_interior_angle` ✓: `para L M → ... → Angle a b c = Angle b c d`

---

## Prop 30 — Transitivity of parallelism ✓
**Milestone:** `para_trans`
> `L ≠ N → para L M → para M N → para L N`
> ✓ PROVED

Helpers proved:
- `online_ne_of_point_line` ✓
- `online_ne_of_line` ✓
- `sameside_of_offline_on_line` ✓
- `right_of_para_right` ✓
- `zero_lt_angle_of_tri` ✓
- `perpendicular_of_not_online` ✓
- `lines_inter_of_not_sameside_distinct` ✓
- `diffside_of_not_online'` ✓
- `pts_line_circle_of_diffside` ✓
- `length_eq_of_oncircle` ✓

Next direction:
- `para` is defined as `∀ e, ¬(OnLine e M ∧ OnLine e N)` — i.e. `¬(A ∧ B)` pointwise. In constructive logic De Morgan does NOT give `¬A ∨ ¬B` from `¬(A ∧ B)`, so this definition is NOT "stronger" than an existential negation; the two forms are constructively equivalent for no-common-point but the disjunctive `¬A ∨ ¬B` form would be strictly stronger and is unavailable here.
- `lines_inter_if_diff_sides` is the key intersection axiom.
- The external perpendicular package is now proved, following Lean’s Prop. 12 route.
- Prop. 30 is now proved by contradiction from a hypothetical common point, using the dropped perpendicular plus Prop. 29 right-angle transfer.
- This fully unlocks the local Prop. 46 helper `lines_inter_of_parallel_through_transversal`.

---

## Prop 31 — Parallel through a point
**Milestone:** `para_of_offline`
> `¬OnLine a M → ∃ N, OnLine a N ∧ para M N`
> TODO

Current status:
- the proof route is in place and checks structurally
- remaining unresolved inputs come from Prop. 23:
  - `angle_copy`
  - `angle_copy'`

---

## Prop 34 — Parallelogram properties
**Milestone:** `len_ang_arelen_ang_area_eq_of_parallelogram`
> `paragram → ab = cd ∧ ∠bad = ∠bcd ∧ area abd = area bcd`
> TODO

Corollaries (all TODO):
- `len_eq_of_parallelogram`: `paragram → length a b = length c d`
- `len_eq_of_parallelogram'`: `paragram → length a d = length c b`
- `len_eq_of_parallelogram''`: `paragram → area a b d = area b c d`

---

## Prop 46 — Constructing a square
**Milestone:** `square_of_len` — proof written; blocked by Props 29–34 TODOs above

Prop 46 local helpers:
- `lines_inter_of_parallel_through_transversal` ✓
- `lines_inter_of_crossing_parallels` ✓ — depends on the above
- `same_side_of_points_on_parallel` ✓

Current direct blockers:
- `para_of_offline`
- `len_ang_arelen_ang_area_eq_of_parallelogram`
- `len_eq_of_parallelogram`
- `len_eq_of_parallelogram'`

Current transitive blockers:
- `angle_copy`
- `angle_copy'`
- `len_ang_arelen_ang_area_eq_of_parallelogram`
- `len_eq_of_parallelogram`
- `len_eq_of_parallelogram'`

---

## Notes
- Some accessory point-construction axioms in nicegeo have unclear derivability from System E, but are geometrically valid.
