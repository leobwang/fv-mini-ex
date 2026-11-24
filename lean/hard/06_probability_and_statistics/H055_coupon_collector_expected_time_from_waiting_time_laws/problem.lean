/- H055 | Coupon collector: expected time from waiting-time laws | 1-1.5 h | geometric law, HasLaw, linearity, tsum, reindexing, mathlib
GOAL
  `n` coupon types. Once `k` types are collected, the failed draws `T k` before a new type follow
  `geometricMeasure p` (law of #failures before the first success) with `p = (n-k)/n`. Prove the
  expected total draws `∑_{k<n} (T k + 1)` is `n · Hₙ`, `Hₙ = ∑_{k<n} 1/(k+1)`. Only the laws are
  assumed, no independence: linearity of expectation does not need it.

REFERENCE
  #check integral_geometricMeasure  -- p ≠ 0 → ∫ n, f n ∂geometricMeasure p = ∑' n, ((1 - p) ^ n * p) • f n
  #check integrable_geometricMeasure_iff  -- p ≠ 0 → (Integrable f _ ↔ Summable fun n => (1 - p) ^ n * p * ‖f n‖)
  #check tsum_coe_mul_geometric_of_norm_lt_one  -- ‖r‖ < 1 → ∑' n, n * r ^ n = r / (1 - r) ^ 2
  #check summable_pow_mul_geometric_of_norm_lt_one  -- (k : ℕ) → ‖r‖ < 1 → Summable fun n => n ^ k * r ^ n
  #check tsum_mul_left  -- ∑' x, a * f x = a * ∑' x, f x
  #check HasLaw.integral_comp  -- HasLaw X P μ → AEStronglyMeasurable f P → ∫ x, (f ∘ X) x ∂μ = ∫ x, f x ∂P
  #check integrable_map_measure  -- AEStronglyMeasurable g (map f μ) → AEMeasurable f μ → (Integrable g (map f μ) ↔ Integrable (g ∘ f) μ)
  example (f : ℕ → ℝ) (P : Measure ℕ) : AEStronglyMeasurable f P := StronglyMeasurable.of_discrete.aestronglyMeasurable
  #check integral_add  -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
  #check integral_const  -- ∫ _, c ∂μ = μ.real Set.univ • c;   `probReal_univ : μ.real Set.univ = 1`
  #check integral_finsetSum  -- (∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ
  #check Finset.sum_range_reflect  -- ∑ j ∈ range n, f (n - 1 - j) = ∑ j ∈ range n, f j
NOTE: `HasLaw X P μ`: `X` is a.e.-measurable and `Measure.map X μ = P` (`hX.map_eq`, `hX.aemeasurable`).
  `∑'` = infinite sum (tsum, 0 if not summable); `‖r‖` = `|r|` on ℝ; `•` = `*` on ℝ (`smul_eq_mul`);
  `μ[f]` = `∫ ω, f ω ∂μ`; `p : unitInterval` has `p.2.1 : 0 ≤ (p : ℝ)`, `p.2.2 : (p : ℝ) ≤ 1`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H055

-- MILESTONE (optional: change or delete)
/-- Mean of the geometric law (failures before the first success). -/
theorem geometric_mean (p : unitInterval) (hp : p ≠ 0) :
    ∫ n, (n : ℝ) ∂(geometricMeasure p) = (1 - p) / p := by
  sorry

-- MILESTONE (optional: change or delete)
theorem geometric_integrable (p : unitInterval) (hp : p ≠ 0) :
    Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure p) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem param_ne_zero (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n) :
    ∀ k < n, p k ≠ 0 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem waiting_time_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    ∀ k < n, Integrable (fun ω => (T k ω : ℝ)) μ := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Expected number of draws (failures + the success) in phase `k`. -/
theorem waiting_time_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    ∀ k < n, μ[fun ω => (T k ω : ℝ) + 1] = (n : ℝ) / (n - k) := by
  sorry

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
H1. Three layers: the mean of one geometric law, transport it to `T k` through `HasLaw`, then sum
    over `k` (linearity) and reindex `∑_{k<n} n/(n-k)` into `n · ∑_{k<n} 1/(k+1)`.
H2. Geometric mean: after `integral_geometricMeasure`, rewrite the summand as `p * (n * (1-p)^n)` (by
    `funext; ring`), pull `p` out with `tsum_mul_left`, apply `tsum_coe_mul_geometric_of_norm_lt_one`
    (`‖1 - p‖ < 1` since `0 < p ≤ 1`), then `field_simp`. Integrability of `T k`: rewrite
    `geometricMeasure (p k)` as `Measure.map (T k) μ` (`← hT.map_eq`) and use `integrable_map_measure`.
H3. `waiting_time_mean`: `integral_add`, `integral_const`, `probReal_univ`, then
    `(hT k hk).integral_comp (f := fun m : ℕ => (m : ℝ)) StronglyMeasurable.of_discrete.aestronglyMeasurable`
    and `field_simp`. Main: `rw [integral_finsetSum _ hint, Finset.sum_congr rfl (… waiting_time_mean …),
    Finset.mul_sum, ← Finset.sum_range_reflect]`, then per term `Nat.cast_sub` (needs `k < n`), `push_cast; ring`.
-/
