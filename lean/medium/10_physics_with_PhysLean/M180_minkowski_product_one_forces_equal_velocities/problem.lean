/- M180 | ⟪u, v⟫ₘ = 1 forces equal 4-velocities | 15-20 min | Velocity subtype, Cauchy–Schwarz, timelike vs null, funext/match, physlib
GOAL
  A 4-velocity `u : Velocity d` is a vector with `⟪u, u⟫ₘ = 1` and time component `u⁰ > 0`. The relative
  Lorentz factor of two 4-velocities is `⟪u, v⟫ₘ`. Show that it equals 1 only when `u = v`.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

open Lorentz Vector

namespace M180

/- SKELETON · eq_zero_of_orth (milestone: prove it FIRST; Part 2 uses it once, in its step 1)
  0. Already in the stub: hu, hw, huw rewritten into components             R1, R2, R3
  1. Cauchy–Schwarz on the spatial parts u⃗, w⃗:                              R4
       hcs : |inner ℝ u⃗ w⃗| ≤ ‖u⃗‖ * ‖w⃗‖
  2. hw0 : w.timeComponent = 0, by contradiction:                            R5
       a. hpos : 0 < w⁰ ^ 2                                                 R6
       b. h1 : (u⁰ * w⁰) ^ 2 ≤ (‖u⃗‖ * ‖w⃗‖) ^ 2
            replace u⁰ * w⁰ by inner ℝ u⃗ w⃗ (huw says they are equal)     R8 (proof inside: R7)
            split hcs into two inequalities, then square                    R9, R10
       c. contradiction from hu, hw, hpos, h1                               R11
  3. hs : w.spatialPart = 0
       rw [hw0] at hw; get ‖w⃗‖ ^ 2 = 0 (R7); then `simpa using` it         R12
       (plain `simp at h; exact h` fails: simp also unfolds w.spatialPart)
  4. w = 0 component by component:                                          R13, R14
       time index:  exact hw0
       space index: the i-th coordinate of hs                               R15, R16
-/
-- MILESTONE (optional: change or delete)
/-- A vector that is null and Minkowski-orthogonal to a timelike vector is zero. -/
theorem eq_zero_of_orth {d : ℕ} (u w : Lorentz.Vector d) (hu : 0 < ⟪u, u⟫ₘ)
    (hw : ⟪w, w⟫ₘ = 0) (huw : ⟪u, w⟫ₘ = 0) : w = 0 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at hu hw
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at huw
  simp only [Real.norm_eq_abs, sq_abs] at hu hw
  -- now hu : 0 < u⁰ ^ 2 - ‖u⃗‖ ^ 2,  hw : w⁰ ^ 2 - ‖w⃗‖ ^ 2 = 0,  huw : u⁰ * w⁰ - inner ℝ u⃗ w⃗ = 0
  sorry

/- SKELETON · eq_of_minkowskiProduct_eq_one
  1. Apply the milestone to u.1 and w = u.1 - v.1; prove its 3 hypotheses inline:   R17
       0 < ⟪u.1, u.1⟫ₘ                  plain `simp`                       R18
       ⟪u.1 - v.1, u.1 - v.1⟫ₘ = 0      expand, swap ⟪v.1, u.1⟫ₘ, use h     R19, R20, R18
       ⟪u.1, u.1 - v.1⟫ₘ = 0            expand, use h                      R19, R18
     result: hw : u.1 - v.1 = 0
  2. Equality of velocities → equality of vectors ↑u = ↑v:                  R21
  3. Close it from hw:                                                      R22
-/
-- BEGIN SPEC
theorem eq_of_minkowskiProduct_eq_one {d : ℕ} (u v : Velocity d) (h : ⟪u.1, v.1⟫ₘ = 1) :
    u = v :=
-- END SPEC
  sorry

end M180

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Look at `w = u.1 - v.1`. By bilinearity and `⟪u.1, u.1⟫ₘ = ⟪v.1, v.1⟫ₘ = ⟪u.1, v.1⟫ₘ = 1` it is null,
    `⟪w, w⟫ₘ = 0`, and orthogonal to the timelike `u.1`, `⟪u.1, w⟫ₘ = 0`. The milestone says such a `w` is `0`.
H2. Milestone, in components (R1–R3): if `w⁰ ≠ 0`, then `u⁰ w⁰ = inner ℝ u⃗ w⃗` and Cauchy–Schwarz (R4) give
    `(u⁰ w⁰)² ≤ ‖u⃗‖² ‖w⃗‖² = ‖u⃗‖² (w⁰)² < (u⁰)² (w⁰)²`, a contradiction (R5, R6, R8–R11). So `w⁰ = 0`, hence
    `‖w⃗‖² = 0` and `w⃗ = 0` (R12); finish by components (R13–R16). Main: apply the milestone with `simp`
    side proofs (R17–R20), then `ext1` (R21) and `sub_eq_zero` (R22).
H3. Main: `have hw := eq_zero_of_orth u.1 (u.1 - v.1) (by simp) (by simp [map_sub, minkowskiProduct_symm v.1 u.1, h])
    (by simp [map_sub, h])`, then `ext1; exact sub_eq_zero.mp hw`. Milestone key step, inside `by_contra h0`:
    `have h1 : (u.timeComponent * w.timeComponent) ^ 2 ≤ (‖u.spatialPart‖ * ‖w.spatialPart‖) ^ 2` by
    `rw [show u.timeComponent * w.timeComponent = inner ℝ u.spatialPart w.spatialPart by linarith]` and
    `exact sq_le_sq' (abs_le.mp hcs).1 (abs_le.mp hcs).2`; with `hpos : 0 < w.timeComponent ^ 2` (`positivity`), `nlinarith`.
-/
