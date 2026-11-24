/- H055 | Coupon collector: expected time from waiting-time laws | 1-1.5 h | geometric law, HasLaw, linearity, tsum, reindexing, mathlib
GOAL
  `n` coupon types; in phase `k < n` the failed draws `T k` before a new type have the law
  `geometricMeasure (p k)` with `p k = (n-k)/n` (no independence assumed). Prove that the expected
  total number of draws `E[∑_{k<n} (T k + 1)]` is `n · Hₙ`, where `Hₙ = ∑_{k<n} 1/(k+1)`.

GUIDE
  Entries R1–R45: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H055

/- SKELETON · geometric_mean   (milestone 1: E[geometric] = (1-p)/p; used in milestone 5)
  1. Integral → series:                                                      R1
  2. Two facts for later steps:
       hp0 : (0 : ℝ) < p        two goals `0 ≤ ↑p` and `0 ≠ ↑p`; the second: `intro h`
                                 (`h : 0 = ↑p`), `apply hp`, then `↑p = ↑0` is `h.symm`:   R4 (R2, R18, R3)
       hr  : ‖(1 - p : ℝ)‖ < 1  norm → abs → two inequalities; `1 - ↑p < 1`
                                 needs `hp0` in the context:                  R5, R6, `constructor`, R7 (R2)
  3. Rewrite the summand so the constant is on the left and the term is
     `↑n * r ^ n`: prove
       e : (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) • (n : ℝ)) = fun n : ℕ => (p : ℝ) * ((n : ℝ) * (1 - p) ^ n)
     by                                                                      R8, R9, `ring`
  4. rw [e], pull out `p`, sum the series, simplify `1 - (1 - p)`:           R10 → R11 → R12
  5. Clear the denominator (`hp0` is in the context):                        R13
-/
-- MILESTONE (optional: change or delete)
/-- Mean of the geometric law (failures before the first success). -/
theorem geometric_mean (p : unitInterval) (hp : p ≠ 0) :
    ∫ n, (n : ℝ) ∂(geometricMeasure p) = (1 - p) / p := by
  sorry

/- SKELETON · geometric_integrable   (milestone 2: E|geometric| < ∞; used in milestone 4)
  1. Integrable → Summable:                                                  R14
  2. `hp0` and then `hr : ‖(1 - p : ℝ)‖ < 1`, exactly as in milestone 1
     (without `hp0`, `linarith` cannot close `1 - ↑p < 1`):                 R4 (R2, R18, R3); R5, R6, `constructor`, R7
  3. Rewrite the summand to `p * (↑n ^ 1 * (1 - p) ^ n)` by a function
     equation `e`:                                                           R8, R15, `ring`
  4. rw [e]; the known summable series, times the constant `p`:              R16 (k = 1) → R17
-/
-- MILESTONE (optional: change or delete)
theorem geometric_integrable (p : unitInterval) (hp : p ≠ 0) :
    Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure p) := by
  sorry

/- SKELETON · param_ne_zero   (milestone 3: p k ≠ 0; used in milestones 4 and 5)
  1. Introduce `k`, `hk : k < n` and `h : p k = 0`; the goal is `False`:     R18
  2. hlt : (k : ℝ) < n:                                                      R19
  3. h0 := hp k hk, then in h0: replace `p k` by `0` (`rw [h]`), then
     `↑0` by `0`, flip, and split the quotient:                              R20, R21, R22 (all `at h0`)
  4. Both cases `↑n - ↑k = 0` and `↑n = 0` contradict `hlt`:                 R23, R7 with R24
-/
-- MILESTONE (optional: change or delete)
theorem param_ne_zero (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n) :
    ∀ k < n, p k ≠ 0 := by
  sorry

/- SKELETON · waiting_time_integrable   (milestone 4: T k integrable; used in milestone 5 and main)
  Needs milestones 2 and 3.
  1. `intro k hk`
  2. hmeas : AEStronglyMeasurable (fun m : ℕ => (m : ℝ)) (Measure.map (T k) μ):   R25
  3. Integrability under `μ` ← integrability under the pushforward,
     with the measurability field of `hT k hk`:                              R27 (hmeas, R26)
  4. Pushforward → `geometricMeasure (p k)`, then milestone 2 (with 3):      R28, `exact`
-/
-- MILESTONE (optional: change or delete)
theorem waiting_time_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    ∀ k < n, Integrable (fun ω => (T k ω : ℝ)) μ := by
  sorry

/- SKELETON · waiting_time_mean   (milestone 5: E[T k + 1] = n/(n-k); used in main)
  Needs milestones 1, 3 and 4.
  1. `intro k hk`
  2. Split off the `+ 1` and evaluate it:                                    R29 (milestone 4, R30) → R31 → R32 → R33
  3. Change of variables, as a hypothesis `h1`, with
     `(f := fun m : ℕ => (m : ℝ))` and the measurability fact; clean it:    R34 (R25), R35
  4. rw [h1, milestone 1 (with milestone 3), hp k hk]
  5. Nonzero facts for `field_simp`: `(k : ℝ) < n`, `(n : ℝ) - k ≠ 0`,
     `(n : ℝ) ≠ 0`:                                                          R19, R7 (R24)
  6. Clear denominators, then `ring`:                                        R13
-/
-- MILESTONE (optional: change or delete)
/-- Expected number of draws (failures + the success) in phase `k`. -/
theorem waiting_time_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    ∀ k < n, μ[fun ω => (T k ω : ℝ) + 1] = (n : ℝ) / (n - k) := by
  sorry

/- SKELETON · coupon_collector
  Prove the milestones first, in order 1 → 5 (3 feeds 4 and 5; 2 feeds 4; 1 and 4 feed 5).
  This proof uses milestones 4 and 5 only.
  1. hint : ∀ k ∈ Finset.range n, Integrable (fun ω => (T k ω : ℝ) + 1) μ
       from milestone 4 (its `k < n` from R36), plus the constant:          R36, R37 (R30)
  2. One `rw`: ∫ ∑ → ∑ ∫; each ∫ by milestone 5 (its `k < n` from R36);
     push `n` into the right sum; reverse the left sum:                      R38 → R39 → R40 → R41 (←)
       goal: ∑ j ∈ range n, ↑n / (↑n - ↑(n - 1 - j)) = ∑ i ∈ range n, ↑n * (1 / (↑i + 1))
  3. Compare term by term; get `k < n`:                                      R42, R36
  4. Remove both truncated subtractions in `n - 1 - k`; side goals by R44:  R43 ×2 (R44)
  5. Numeral casts, then `ring`:                                             R45
-/
-- BEGIN SPEC
theorem coupon_collector {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    μ[fun ω => ∑ k ∈ Finset.range n, ((T k ω : ℝ) + 1)] =
      n * ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) :=
-- END SPEC
  sorry

end H055

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three layers: the mean of one geometric law (milestones 1, 2), transport to `T k` through `HasLaw`
    (milestones 4, 5; 3 supplies `p k ≠ 0`), then linearity over `k` and reversing the sum
    `∑_{k<n} n/(n-k)` into `n · ∑_{k<n} 1/(k+1)` (main). Independence is never used.
H2. Milestone 1: `integral_geometricMeasure` (R1), rewrite the summand to `p * (↑n * (1 - p) ^ n)` with a
    `have e … := by funext n; rw [smul_eq_mul]; ring`, then `tsum_mul_left`,
    `tsum_coe_mul_geometric_of_norm_lt_one hr`, `sub_sub_cancel`, `field_simp` (R10–R13).
    Milestone 4: `(integrable_map_measure hmeas (hT k hk).aemeasurable).1`, then `rw [(hT k hk).map_eq]`.
    Milestone 5: `integral_add`, `integral_const`, `probReal_univ`, `one_smul`, then `HasLaw.integral_comp`.
    Main: `integral_finsetSum`, `Finset.sum_congr` with milestone 5, `Finset.mul_sum`, `← Finset.sum_range_reflect`.
H3. `hr : ‖(1 - p : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]`
    (with `hp0 : (0 : ℝ) < p` already in the context, in milestones 1 and 2).
    Milestone 5: `have h1 := (hT k hk).integral_comp (f := fun m : ℕ => (m : ℝ))
    StronglyMeasurable.of_discrete.aestronglyMeasurable`, then `simp only [Function.comp_def] at h1`.
    Main, per term: `rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring`
    (`n - 1 - k` is truncated `ℕ` subtraction; `k < n` makes both casts exact).
-/
