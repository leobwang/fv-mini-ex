/- M177 | Time dilation, with its equality case | 15-20 min | properTime, Real.sqrt, sums of squares, Finset.sum_eq_zero_iff_of_nonneg, physlib
GOAL
  For events `q`, `p` with coordinate-time gap `Δt = (p - q)⁰ > 0`, the proper time
  `τ = √⟪p - q, p - q⟫ₘ` satisfies `τ ≤ Δt`, and `τ = Δt` iff `p`, `q` have the same spatial coordinates.
BANNED: Lorentz.Vector.minkowskiProduct_self_le_timeComponent_sq, Lorentz.Vector.timelike_time_dominates_space

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.Special.ProperTime

open Lorentz Vector

namespace M177

/- SKELETON · properTime_le
  1. Unfold τ and name the difference v := p - q (this also rewrites h):    R1, R2
  2. Two facts BEFORE splitting, so all three branches see them:
       key : ⟪v, v⟫ₘ = v (Sum.inl 0) ^ 2 - ∑ i, v (Sum.inr i) ^ 2         R3, then simp with R4
       hs  : 0 ≤ ∑ i, v (Sum.inr i) ^ 2                                  R6 with R5
  3. Split into τ ≤ Δt, (→) with `he`, (←) with `hi`:                       R7
  4. τ ≤ Δt: rewrite √ ≤ (side condition from h)                           R9 with R8
             then the linear consequence of key, hs                        R10
  5. (→) he : √⟪v, v⟫ₘ = v (Sum.inl 0)
       a. hpos : 0 ≤ ⟪v, v⟫ₘ by contradiction: if negative, √ is 0 in he   R11, R12 → R8 → R13, R10
       b. h2 : ⟪v, v⟫ₘ = v (Sum.inl 0) ^ 2                                 rw [← he], R14
       c. hz : ∑ i, v (Sum.inr i) ^ 2 = 0  (from key, h2)                  R10
       d. intro i; the i-th square is 0, so the i-th component is 0        R15 (with R5, R16), R17
       e. back from v to p, q                                              R20 (with hv, R18, R19)
  6. (←) hi : ∀ i, p (Sum.inr i) = q (Sum.inr i)
       a. hz : ∑ i, v (Sum.inr i) ^ 2 = 0, each term by simp [hv, hi i]    R21 (R18 inside)
       b. rw [key, hz], then                                              R22, R23 (side condition: R8)
-/
-- BEGIN SPEC
theorem properTime_le {d : ℕ} (q p : SpaceTime d) (h : 0 < (p - q) (Sum.inl 0)) :
    SpaceTime.properTime q p ≤ (p - q) (Sum.inl 0) ∧
      (SpaceTime.properTime q p = (p - q) (Sum.inl 0) ↔ ∀ i, p (Sum.inr i) = q (Sum.inr i)) :=
-- END SPEC
  sorry

end M177

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With `v = p - q`: `⟪v, v⟫ₘ = (v⁰)² - ∑ i, (vⁱ)²`, and the sum of squares is `≥ 0`. All three parts
    follow from these two facts plus three facts about `√`: `√x ≤ y ↔ x ≤ y²` (for `y ≥ 0`), `√x = 0` for
    `x ≤ 0`, and `√(y²) = y` (for `y ≥ 0`).
H2. `unfold`, `set v := p - q with hv`, prove `key` and `hs`, then `refine ⟨?_, ⟨fun he => ?_, fun hi => ?_⟩⟩`.
    Part 1: `Real.sqrt_le_left h.le`, then `linarith`. (→): first `0 ≤ ⟪v, v⟫ₘ` by contradiction (else
    `τ = 0 < Δt`); square `he` to get `⟪v, v⟫ₘ = (v⁰)²`, so `∑ = 0`, so each square is `0`
    (`Finset.sum_eq_zero_iff_of_nonneg`), so each `vⁱ = 0` (`pow_eq_zero_iff`). (←): the sum is `0`
    (`Finset.sum_eq_zero`), so `τ = √((v⁰)²) = v⁰`.
H3. `key` is `by rw [minkowskiProduct_toCoord]; simp [sq]`; `hs := Finset.sum_nonneg (fun i _ => sq_nonneg _)`.
    In (→): `rw [Real.sqrt_eq_zero'.mpr (le_of_lt (not_le.mp hneg))] at he` inside `by_contra hneg`;
    `h2 := by rw [← he, Real.sq_sqrt hpos]`; finish with `simpa [hv, sub_eq_zero] using h4`.
    (←) ends with `rw [key, hz, sub_zero, Real.sqrt_sq h.le]`.
-/
