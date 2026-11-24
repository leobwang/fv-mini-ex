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
  rw [integral_geometricMeasure hp]
  have hp0 : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  have hr : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]
  have e : (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) • (n : ℝ)) =
      fun n : ℕ => (p : ℝ) * ((n : ℝ) * (1 - p) ^ n) := by
    funext n; rw [smul_eq_mul]; ring
  rw [e, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hr, sub_sub_cancel]
  field_simp

-- MILESTONE (optional: change or delete)
theorem geometric_integrable (p : unitInterval) (hp : p ≠ 0) :
    Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure p) := by
  rw [integrable_geometricMeasure_iff hp]
  have hp0 : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  have hr : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]
  have e : (fun n : ℕ => (1 - (p : ℝ)) ^ n * p * ‖(n : ℝ)‖) =
      fun n : ℕ => (p : ℝ) * ((n : ℝ) ^ 1 * (1 - p) ^ n) := by
    funext n; rw [Real.norm_natCast]; ring
  rw [e]
  exact (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left (p : ℝ)

-- MILESTONE (optional: change or delete)
theorem param_ne_zero (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n) :
    ∀ k < n, p k ≠ 0 := by
  intro k hk h
  have hlt : (k : ℝ) < n := by exact_mod_cast hk
  have h0 := hp k hk
  rw [h, Set.Icc.coe_zero, eq_comm, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0 <;> linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

-- MILESTONE (optional: change or delete)
theorem waiting_time_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    ∀ k < n, Integrable (fun ω => (T k ω : ℝ)) μ := by
  intro k hk
  have hmeas : AEStronglyMeasurable (fun m : ℕ => (m : ℝ)) (Measure.map (T k) μ) :=
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine (integrable_map_measure hmeas (hT k hk).aemeasurable).1 ?_
  rw [(hT k hk).map_eq]
  exact geometric_integrable (p k) (param_ne_zero n p hp k hk)

-- MILESTONE (optional: change or delete)
/-- Expected number of draws (failures + the success) in phase `k`. -/
theorem waiting_time_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    ∀ k < n, μ[fun ω => (T k ω : ℝ) + 1] = (n : ℝ) / (n - k) := by
  intro k hk
  rw [integral_add (waiting_time_integrable μ n p hp T hT k hk) (integrable_const 1),
    integral_const, probReal_univ, one_smul]
  have h1 := (hT k hk).integral_comp (f := fun m : ℕ => (m : ℝ))
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  rw [h1, geometric_mean (p k) (param_ne_zero n p hp k hk), hp k hk]
  have : (k : ℝ) < n := by exact_mod_cast hk
  have : (n : ℝ) - k ≠ 0 := by linarith
  have : (n : ℝ) ≠ 0 := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  field_simp
  ring

-- BEGIN SPEC
theorem coupon_collector {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (p : ℕ → unitInterval) (hp : ∀ k < n, (p k : ℝ) = (n - k) / n)
    (T : ℕ → Ω → ℕ) (hT : ∀ k < n, HasLaw (T k) (geometricMeasure (p k)) μ) :
    μ[fun ω => ∑ k ∈ Finset.range n, ((T k ω : ℝ) + 1)] =
      n * ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) :=
-- END SPEC
  by
    have hint : ∀ k ∈ Finset.range n, Integrable (fun ω => (T k ω : ℝ) + 1) μ := fun k hk =>
      (waiting_time_integrable μ n p hp T hT k (Finset.mem_range.1 hk)).add (integrable_const 1)
    rw [integral_finsetSum _ hint,
      Finset.sum_congr rfl (fun k hk => waiting_time_mean μ n p hp T hT k (Finset.mem_range.1 hk)),
      Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk := Finset.mem_range.1 hk
    -- WHY: `n - 1 - k` is truncated ℕ subtraction; `k < n` makes both casts exact.
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring

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
