/- M087 | Cantelli's one-sided inequality | 15-20 min | Markov, shifted second moment, optimisation, nlinarith, mathlib
GOAL
  One-sided Chebyshev: for `t > 0`, `P(X - E X ≥ t) ≤ σ² / (σ² + t²)` where `σ² = Var X`.
  Prove the milestone (Markov applied to `(X - E X + u)²` for a shift `u ≥ 0`), then pick the best `u`.

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M087

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
-- END SPEC

/- SKELETON · shifted_markov   (milestone; prove it FIRST; cantelli applies it at u = Var[X; μ] / t)
  Below, Y ω is `(X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2` (that is (X ω - m + u)²); write it
  out in Lean, identically everywhere (cheatsheet Traps).
  1. Name the mean m := μ[X], with hm : μ[X] = m:                               R1
     Facts:  hXi : Integrable X μ                                               R2
             hvar : ∫ ω, (X ω - m) ^ 2 ∂μ = Var[X; μ]                           R3, R4, rw [hm]
     Then rw [hm] in the goal.
  2. Integrability, each a `have` stated in lambda form:
       i1 : the (X ω - m) ^ 2 part                                              R5 → R6
       i2 : the (2 * u) * (X ω - m) part                                        R8 with R7, then R9
       i3 : i1's + i2's integrand                                               R8 (`add`)
       hYi : Y                                                                  R8 (`add`) with R7
  3. hE : ∫ ω, Y ω ∂μ = Var[X; μ] + u ^ 2:
       split off u ^ 2, then split i1 + i2                                      R10, R10
       pull out 2 * u, split X ω - m                                            R11, R12
       rw [hvar, hm], then the constants                                        R13
  4. Markov: hmk := Markov for Y at level (t + u) ^ 2                           R14
       its a.e. argument: R15, restate with `show (0 : ℝ) ≤ Y ω`, prove by      R17 with R16
     Put hE into it:                                                            R18
  5. hsub : {ω | t ≤ X ω - m} ⊆ {ω | (t + u) ^ 2 ≤ Y ω}:                         R19, R20, R17
  6. Finish:                                                                    R17 with R21 on hsub, R16
-/
-- MILESTONE (optional: change or delete)
-- Markov on `(X - E X + u)²`: on the event `t ≤ X - E X` that square is at least `(t + u)²`
theorem shifted_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | t ≤ X ω - μ[X]} * (t + u) ^ 2 ≤ Var[X; μ] + u ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, μ[X] = m := ⟨_, rfl⟩
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hvar : ∫ ω, (X ω - m) ^ 2 ∂μ = Var[X; μ] := by
    rw [variance_eq_integral hX.aemeasurable, hm]
  rw [hm]
  have i1 : Integrable (fun ω => (X ω - m) ^ 2) μ := (hX.sub (memLp_const _)).integrable_sq
  have i2 : Integrable (fun ω => (2 * u) * (X ω - m)) μ :=
    (hXi.sub (integrable_const _)).const_mul _
  have i3 : Integrable (fun ω => (X ω - m) ^ 2 + (2 * u) * (X ω - m)) μ := i1.add i2
  have hYi : Integrable (fun ω => (X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2) μ :=
    i3.add (integrable_const _)
  have hE : ∫ ω, (X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2 ∂μ = Var[X; μ] + u ^ 2 := by
    rw [integral_add i3 (integrable_const _), integral_add i1 i2, integral_const_mul,
      integral_sub hXi (integrable_const _), hvar, hm]
    simp
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω =>
      show (0 : ℝ) ≤ (X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2 by
        nlinarith [sq_nonneg (X ω - m + u)]) hYi ((t + u) ^ 2)
  rw [hE] at hmk
  have hsub : {ω | t ≤ X ω - m} ⊆
      {ω | (t + u) ^ 2 ≤ (X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith
  nlinarith [measureReal_mono (μ := μ) hsub, sq_nonneg (t + u)]

/- SKELETON · cantelli
  0. Prove the milestone shifted_markov first.
  1. hk : the milestone at u = Var[X; μ] / t; its `0 ≤ u` argument:            R24 with R22, R23
  2. Name the variance v, with hv : Var[X; μ] = v:                              R1
       hv0 : 0 ≤ v                                                              R25 with R22
       rewrite hv in hk and in the goal                                         R18
  3. Two facts, each by R26 then `ring`:
       e1 : (t + v / t) ^ 2 = (v + t ^ 2) ^ 2 / t ^ 2
       e2 : v + (v / t) ^ 2 = v * (v + t ^ 2) / t ^ 2
  4. In hk: rw [e1, e2], then both sides over t ^ 2, then cancel it:           R18, R27, R28 with R29
  5. hpos : 0 < v + t ^ 2                                                       R29
     Clear the goal's denominator, finish:                                      R30 with hpos, R17
-/
-- BEGIN SPEC
theorem cantelli {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t ≤ X ω - μ[X]} ≤ Var[X; μ] / (Var[X; μ] + t ^ 2) :=
-- END SPEC
  by
    have hk := shifted_markov μ X hX t ht (Var[X; μ] / t) (div_nonneg (variance_nonneg X μ) ht.le)
    obtain ⟨v, hv⟩ : ∃ v, Var[X; μ] = v := ⟨_, rfl⟩
    have hv0 : 0 ≤ v := hv ▸ variance_nonneg X μ
    rw [hv] at hk ⊢
    have e1 : (t + v / t) ^ 2 = (v + t ^ 2) ^ 2 / t ^ 2 := by field_simp; ring
    have e2 : v + (v / t) ^ 2 = v * (v + t ^ 2) / t ^ 2 := by field_simp; ring
    rw [e1, e2, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)] at hk
    have hpos : 0 < v + t ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    nlinarith

end M087

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Milestone: with `m := μ[X]`, `Y = (X - m + u)² ≥ 0` has `E Y = Var X + u²` because `E[X - m] = 0`, and
    on the event `t ≤ X - m` (with `t + u ≥ 0`) `Y ≥ (t + u)²`: Markov for `Y` at level `(t + u)²`.
    Main: `P(A) ≤ (v + u²)/(t + u)²` is smallest at `u = v / t` where `v := Var[X; μ]`.
H2. Milestone: write `Y` expanded, `(X ω - m) ^ 2 + (2 * u) * (X ω - m) + u ^ 2`; prove its integrability
    piece by piece in lambda form (R5–R9), compute its integral by `integral_add`/`integral_const_mul`/
    `integral_sub` (R10–R13), apply `mul_meas_ge_le_integral_of_nonneg` (R14), then compare the events with
    `measureReal_mono` (R21) inside `nlinarith`. Main: apply the milestone at `u = v / t`, rewrite both sides
    over `t ^ 2`, cancel, and clear the denominator `v + t ^ 2`.
H3. `hmk := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω =>
    show (0 : ℝ) ≤ Y ω by nlinarith [sq_nonneg (X ω - m + u)]) hYi ((t + u) ^ 2)`; the milestone ends
    `nlinarith [measureReal_mono (μ := μ) hsub, sq_nonneg (t + u)]`. Main: with `e1`, `e2` (`field_simp; ring`),
    `rw [e1, e2, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)] at hk`, then
    `rw [le_div_iff₀ hpos]; nlinarith` with `hpos : 0 < v + t ^ 2`.
-/
