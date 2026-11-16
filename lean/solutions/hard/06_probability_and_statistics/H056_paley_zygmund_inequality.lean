/- H056 | Paley–Zygmund inequality | 1-1.5 h | second moment method, Cauchy–Schwarz, indicators, integral_mono, mathlib
GOAL
  For `X ≥ 0` with `E[X²] < ∞` and `0 ≤ θ ≤ 1`: `P(X > θ E X) ≥ (1 - θ)² (E X)² / E[X²]` (stated
  without division). Split `E X` on the event `A = {X > θ E X}`, then bound `E[X 1_A]` by Cauchy–Schwarz.

REFERENCE
  `μ[f]` is `∫ ω, f ω ∂μ`;  `μ.real A : ℝ` is P(A);  `A.indicator 1 ω` is `1_A(ω)`: `1` on `A`, `0` off it.
  #check Set.indicator_apply     -- s.indicator f a = if a ∈ s then f a else 0
  #check integral_indicator_one  -- MeasurableSet s → ∫ x, s.indicator 1 x ∂μ = μ.real s
  #check integral_mono           -- Integrable f μ → Integrable g μ → f ≤ g → ∫ f ∂μ ≤ ∫ g ∂μ   (`f ≤ g` is `∀ ω, …`)
  #check measurableSet_lt        -- Measurable f → Measurable g → MeasurableSet {a | f a < g a}
  #check MemLp.integrable_sq     -- MemLp f 2 μ → Integrable (fun x => f x ^ 2) μ;  `hX.integrable one_le_two` : Integrable X μ
  #check Integrable.mul_bdd      -- Integrable f μ → AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, ‖g x‖ ≤ c) → Integrable (fun x => f x * g x) μ
  #check Measurable.indicator    -- Measurable f → MeasurableSet s → Measurable (s.indicator f);  then `.aestronglyMeasurable`
  #check pow_le_pow_left₀        -- 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n
  #check discrim_le_zero         -- (∀ x, 0 ≤ a * (x * x) + b * x + c) → discrim a b c ≤ 0;  then `rw [discrim] at h`
  -- Cauchy–Schwarz as in M090: discriminant of `t ↦ E[(X - t 1_A)²] ≥ 0`, using `1_A² = 1_A` (Hölder also allowed).
NOTE: state integrability as `Integrable (fun ω => X ω * A.indicator 1 ω) μ` (lambda form) before `rw [integral_add …]`.
-/
import Mathlib

namespace H056

open MeasureTheory ProbabilityTheory

-- MILESTONE (optional: change or delete)
theorem split_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X) (hX : MemLp X 2 μ) (hnn : ∀ ω, 0 ≤ X ω) (θ : ℝ) (hθ : 0 ≤ θ) :
    μ[X] ≤ θ * μ[X] + ∫ ω, X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω ∂μ := by
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hA : MeasurableSet {ω | θ * μ[X] < X ω} := measurableSet_lt measurable_const hmeas
  have hI : Integrable (fun ω => X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω) μ := by
    refine hXi.mul_bdd (c := 1) (measurable_const.indicator hA).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    by_cases h : θ * μ[X] < X ω <;> simp [Set.indicator, h]
  calc μ[X] ≤ ∫ ω, (θ * μ[X] + X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω) ∂μ := by
        refine integral_mono hXi ((integrable_const _).add hI) fun ω => ?_
        by_cases h : θ * μ[X] < X ω
        · simp [Set.indicator, h]
          exact mul_nonneg hθ (integral_nonneg hnn)
        · -- WHY: off the event we need `X ω ≤ θ E X + 0`, which is exactly `¬ (θ E X < X ω)`.
          simp [Set.indicator, h]
          linarith
    _ = _ := by rw [integral_add (integrable_const _) hI]; simp

-- MILESTONE (optional: change or delete)
theorem cs_indicator {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, X ω * A.indicator 1 ω ∂μ) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ.real A := by
  have hX2 := hX.integrable_sq
  have h1 : Integrable (fun ω => X ω * A.indicator 1 ω) μ :=
    (hX.integrable one_le_two).mul_bdd (c := 1)
      (measurable_const.indicator hA).aestronglyMeasurable
      (ae_of_all _ fun ω => by by_cases h : ω ∈ A <;> simp [Set.indicator, h])
  have hi : Integrable (A.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hA
  have hsq : ∀ ω, A.indicator (1 : Ω → ℝ) ω ^ 2 = A.indicator 1 ω := fun ω => by
    by_cases h : ω ∈ A <;> simp [Set.indicator, h]
  have key : ∀ t : ℝ, 0 ≤ μ.real A * (t * t) + (-2 * ∫ ω, X ω * A.indicator 1 ω ∂μ) * t
      + μ[fun ω => X ω ^ 2] := by
    intro t
    have e : (fun ω => (X ω - t * A.indicator 1 ω) ^ 2) = fun ω =>
        X ω ^ 2 + ((-2 * t) * (X ω * A.indicator 1 ω) + (t * t) * A.indicator (1 : Ω → ℝ) ω) := by
      funext ω
      linear_combination (t * t) * hsq ω
    have h0 : 0 ≤ ∫ ω, (X ω - t * A.indicator (1 : Ω → ℝ) ω) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    have ia : Integrable (fun ω => (-2 * t) * (X ω * A.indicator 1 ω)) μ := h1.const_mul _
    have ib : Integrable (fun ω => (t * t) * A.indicator (1 : Ω → ℝ) ω) μ := hi.const_mul _
    have iab : Integrable (fun ω => (-2 * t) * (X ω * A.indicator 1 ω)
        + (t * t) * A.indicator (1 : Ω → ℝ) ω) μ := ia.add ib
    rw [e, integral_add hX2 iab, integral_add ia ib, integral_const_mul,
      integral_const_mul, integral_indicator_one hA] at h0
    linarith
  have := discrim_le_zero key
  rw [discrim] at this
  nlinarith

-- BEGIN SPEC
theorem paley_zygmund {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X) (hX : MemLp X 2 μ) (hnn : ∀ ω, 0 ≤ X ω)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (μ[X]) ^ 2 ≤ μ[fun ω => X ω ^ 2] * μ.real {ω | θ * μ[X] < X ω} :=
-- END SPEC
  by
    have h1 := split_mean μ X hmeas hX hnn θ hθ0
    have h3 : 0 ≤ (1 - θ) * μ[X] := mul_nonneg (by linarith) (integral_nonneg hnn)
    calc (1 - θ) ^ 2 * (μ[X]) ^ 2 = ((1 - θ) * μ[X]) ^ 2 := by ring
      _ ≤ (∫ ω, X ω * {ω | θ * μ[X] < X ω}.indicator 1 ω ∂μ) ^ 2 :=
          pow_le_pow_left₀ h3 (by linarith) 2
      _ ≤ _ := cs_indicator μ X hX _ (measurableSet_lt measurable_const hmeas)

end H056

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Pointwise, `X ω ≤ θ E X + X ω · 1_A(ω)`: on `A` the indicator is `1`; off `A`, `X ω ≤ θ E X`.
    Integrating gives `(1 - θ) E X ≤ E[X 1_A]`, and Cauchy–Schwarz gives `E[X 1_A]² ≤ E[X²] P(A)`.
H2. `split_mean`: `integral_mono` against `fun ω => θ * μ[X] + X ω * A.indicator 1 ω`, prove the pointwise
    bound by `by_cases h : θ * μ[X] < X ω` then `simp [Set.indicator, h]`, and split the right integral with
    `integral_add (integrable_const _) hI`. `cs_indicator`: as in M090, prove
    `∀ t, 0 ≤ μ.real A * (t * t) + (-2 * ∫ ω, X ω * A.indicator 1 ω ∂μ) * t + μ[fun ω => X ω ^ 2]`.
H3. Main: `0 ≤ (1 - θ) * μ[X]` (`integral_nonneg hnn`), then
    `calc (1 - θ) ^ 2 * μ[X] ^ 2 = ((1 - θ) * μ[X]) ^ 2 := by ring
      _ ≤ (∫ ω, X ω * A.indicator 1 ω ∂μ) ^ 2 := pow_le_pow_left₀ h3 (by linarith [split_mean …]) 2
      _ ≤ _ := cs_indicator μ X hX _ (measurableSet_lt measurable_const hmeas)`.
-/
