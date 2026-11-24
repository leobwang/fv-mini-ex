/- M087 | Cantelli's one-sided inequality | 15-20 min | Markov, shifted second moment, optimisation, nlinarith, mathlib
GOAL
  One-sided Chebyshev: for `t > 0`, `P(X - E X ≥ t) ≤ σ² / (σ² + t²)` where `σ² = Var X`.
  Prove the milestone (Markov applied to `(X - E X + u)²` for a shift `u ≥ 0`), then pick the best `u`.

REFERENCE
  `μ.real s : ℝ` is the probability of `s`; `μ[X]` is `∫ ω, X ω ∂μ`; `MemLp X 2 μ`: `E[X²] < ∞`.
  `Var[X; μ]` is the variance of `X` under `μ` (`ProbabilityTheory.variance X μ`).
  #check mul_meas_ge_le_integral_of_nonneg  -- 0 ≤ᵐ[μ] f → Integrable f μ → ∀ ε, ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ
  #check variance_eq_integral  -- AEMeasurable X μ → Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
  #check variance_nonneg       -- (X μ) → 0 ≤ Var[X; μ]
  #check measureReal_mono      -- s₁ ⊆ s₂ → μ.real s₁ ≤ μ.real s₂   (finite μ)
  #check integral_add          -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ f + ∫ g  (also integral_sub)
  #check integral_const_mul    -- ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
  example (hX : MemLp X 2 μ) : Integrable X μ := hX.integrable one_le_two  -- `(hX.sub (memLp_const m)).integrable_sq`
  example (X : Ω → ℝ) : ∃ v, Var[X; μ] = v := ⟨_, rfl⟩  -- `obtain ⟨v, hv⟩ := ...` names a big term
NOTE: `rw [integral_add hf hg]` matches only when `hf`, `hg` are stated as `Integrable (fun ω => ...) μ`.
-/
import Mathlib

namespace M087

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory
-- END SPEC

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
H1. Milestone: with `m := μ[X]`, `E[(X - m + u)²] = Var X + u²` because `E[X - m] = 0`, and on the event
    `t ≤ X - m` (with `t + u ≥ 0`) the square is at least `(t + u)²`. Main: apply it at the best `u`.
H2. Milestone: Markov on `fun ω => (X ω - m) ^ 2 + 2 * u * (X ω - m) + u ^ 2` at level `(t + u) ^ 2`
    (its integral splits by `integral_add`/`integral_sub`), then `measureReal_mono` for the events.
    Main: use `u = v / t` where `v := Var[X; μ]`.
H3. With `u = v / t`: `(t + v / t) ^ 2 = (v + t ^ 2) ^ 2 / t ^ 2` and `v + (v / t) ^ 2 = v * (v + t ^ 2) / t ^ 2`
    (`field_simp; ring`); cancel `t ^ 2`; with `hpos : 0 < v + t ^ 2`, `rw [le_div_iff₀ hpos]; nlinarith`.
-/
