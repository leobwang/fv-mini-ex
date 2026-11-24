/- H060 | Random-walk martingales | 1.5-2 h | Martingale, natural filtration, condExp, independence, pull-out, mathlib
GOAL
  Independent, integrable, mean-zero steps `X 0, X 1, …`; the walk is `Sₙ = X 0 + … + X n`. Show `S` is a
  martingale for the natural filtration `ℱₙ = σ(X 0, …, X n)` (what is known after step `n`): adapted,
  integrable, and `E[Sₙ₊₁ - Sₙ | ℱₙ] = 0`. For `±1` steps, show `Sₙ² - (n + 1)` is a martingale too.

REFERENCE
  `Filtration.natural X hX n`: ℱₙ;  `StronglyMeasurable[m] f`: f is m-measurable;  `μ[f | m]`: E[f | m]
  `f =ᵐ[μ] g`: f = g a.e.;  `mΩ`: the ambient `MeasurableSpace Ω`;  `Indep m₁ m₂ μ`: σ-algebras m₁, m₂ independent
  #check martingale_of_condExp_sub_eq_zero_nat  -- StronglyAdapted 𝒢 f → (∀ i, Integrable (f i) μ) →
    --   (∀ i, μ[f (i+1) - f i | 𝒢 i] =ᵐ[μ] 0) → Martingale f 𝒢 μ;  `StronglyAdapted`: each f n is 𝒢ₙ-measurable
  #check Filtration.stronglyAdapted_natural  -- X i is ℱᵢ-measurable; `(Filtration.natural X hX).mono : i ≤ j → ℱᵢ ≤ ℱⱼ`
  #check Finset.stronglyMeasurable_fun_sum  -- all `f i` m-measurable → so is `fun a => ∑ i ∈ s, f i a`
  #check iIndepFun.indep_comap_natural_of_lt  -- iIndepFun X μ → i < j → Indep σ(X j) ℱᵢ μ;  σ(X j) = `.comap (X j) _`
  #check condExp_indep_eq -- m₁ ≤ mΩ → m₂ ≤ mΩ → StronglyMeasurable[m₁] f → Indep m₁ m₂ μ → μ[f | m₂] =ᵐ[μ] fun _ => μ[f]
  #check condExp_mul_of_stronglyMeasurable_left  -- StronglyMeasurable[m] f → Integrable (f * g) μ → Integrable g μ →
    --   μ[f * g | m] =ᵐ[μ] f * μ[g | m]  (pull-out);  `integrable_finsetSum`: finite sums of integrables
  #check Integrable.of_bound  -- AEStronglyMeasurable f μ → ∀ C, (∀ᵐ x ∂μ, ‖f x‖ ≤ C) → Integrable f μ  (`.mul_bdd`)
  `h₁.trans h₂` chains `=ᵐ`;  `filter_upwards [h] with ω hω` makes an `=ᵐ` goal pointwise;  `ae_of_all μ h`: ∀ᵐ from ∀
BANNED: condExp_natural_ae_eq_of_lt
-/
import Mathlib

namespace H060

open MeasureTheory ProbabilityTheory

-- MILESTONE (optional: change or delete)
theorem partial_sum_adapted {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, StronglyMeasurable (X i)) (n : ℕ) :
    StronglyMeasurable[Filtration.natural X hX n] (fun ω => ∑ i ∈ Finset.range (n + 1), X i ω) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact (Filtration.stronglyAdapted_natural hX i).mono
    ((Filtration.natural X hX).mono (Finset.mem_range_succ_iff.mp hi))

-- MILESTONE (optional: change or delete)
theorem increment_condExp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, StronglyMeasurable (X i))
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0) (n : ℕ) :
    μ[X (n + 1) | Filtration.natural X hX n] =ᵐ[μ] 0 := by
  have h := condExp_indep_eq (hX (n + 1)).measurable.comap_le (Filtration.le _ n)
    (comap_measurable (X (n + 1))).stronglyMeasurable
    (hindep.indep_comap_natural_of_lt hX n.lt_succ_self)
  rw [hmean] at h
  exact h

-- MILESTONE (optional: change or delete)
theorem sq_increment (X : ℕ → ℝ) (n : ℕ) (h : X (n + 1) ^ 2 = 1) :
    (∑ i ∈ Finset.range (n + 1 + 1), X i) ^ 2 - ((n + 1 : ℕ) + 1 : ℝ)
      - ((∑ i ∈ Finset.range (n + 1), X i) ^ 2 - (n + 1))
      = 2 * (∑ i ∈ Finset.range (n + 1), X i) * X (n + 1) := by
  rw [Finset.sum_range_succ _ (n + 1)]
  push_cast
  linear_combination h

-- BEGIN SPEC
theorem walk_martingale {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, StronglyMeasurable (X i)) (hint : ∀ i, Integrable (X i) μ)
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0) :
    Martingale (fun n ω => ∑ i ∈ Finset.range (n + 1), X i ω) (Filtration.natural X hX) μ :=
-- END SPEC
  by
    apply martingale_of_condExp_sub_eq_zero_nat
    · exact partial_sum_adapted X hX
    · exact fun n => integrable_finsetSum _ fun i _ => hint i
    · intro n
      -- WHY: the increment `S (n+1) - S n` is just `X (n+1)`
      have e : (fun ω => ∑ i ∈ Finset.range (n + 1 + 1), X i ω)
          - (fun ω => ∑ i ∈ Finset.range (n + 1), X i ω) = X (n + 1) := by
        funext ω
        simp [Finset.sum_range_succ _ (n + 1)]
      rw [e]
      exact increment_condExp μ X hX hindep hmean n

-- BEGIN SPEC
theorem walk_sq_martingale {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, StronglyMeasurable (X i)) (hpm : ∀ i ω, X i ω = 1 ∨ X i ω = -1)
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0) :
    Martingale (fun n ω => (∑ i ∈ Finset.range (n + 1), X i ω) ^ 2 - (n + 1))
      (Filtration.natural X hX) μ :=
-- END SPEC
  by
    have hb : ∀ i ω, |X i ω| ≤ 1 := fun i ω => by rcases hpm i ω with h | h <;> simp [h]
    have hsq : ∀ i ω, X i ω ^ 2 = 1 := fun i ω => by rcases hpm i ω with h | h <;> simp [h]
    have hint : ∀ i, Integrable (X i) μ := fun i =>
      Integrable.of_bound (hX i).aestronglyMeasurable 1 (ae_of_all _ fun ω => hb i ω)
    set S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1), X i ω with hS
    have hSm : ∀ n, StronglyMeasurable[Filtration.natural X hX n] (S n) :=
      partial_sum_adapted X hX
    -- `|S n| ≤ n + 1`, so `S n` and `(S n)²` are bounded, hence integrable
    have hSb : ∀ n ω, |S n ω| ≤ n + 1 := by
      intro n ω
      calc |S n ω| ≤ ∑ i ∈ Finset.range (n + 1), |X i ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (n + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => hb i ω
        _ = n + 1 := by simp
    have hSae : ∀ n, AEStronglyMeasurable (S n) μ := fun n =>
      ((hSm n).mono ((Filtration.natural X hX).le n)).aestronglyMeasurable
    have hSi : ∀ n, Integrable (S n) μ := fun n =>
      Integrable.of_bound (hSae n) (n + 1) (ae_of_all _ fun ω => hSb n ω)
    apply martingale_of_condExp_sub_eq_zero_nat
    · intro n
      exact ((hSm n).pow 2).sub stronglyMeasurable_const
    · intro n
      have h2 : Integrable (fun ω => S n ω ^ 2) μ :=
        Integrable.of_bound ((hSae n).pow 2) ((n + 1) ^ 2) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hSb n ω) 2)
      exact h2.sub (integrable_const _)
    · intro n
      have e : ((fun ω => S (n + 1) ω ^ 2 - ((n + 1 : ℕ) + 1 : ℝ)) - fun ω => S n ω ^ 2 - (n + 1))
          = (fun ω => 2 * S n ω) * X (n + 1) := by
        funext ω
        exact sq_increment (fun i => X i ω) n (hsq (n + 1) ω)
      rw [e]
      have hprod : Integrable ((fun ω => 2 * S n ω) * X (n + 1)) μ :=
        ((hSi n).const_mul 2).mul_bdd (hX (n + 1)).aestronglyMeasurable
          (ae_of_all _ fun ω => hb (n + 1) ω)
      refine (condExp_mul_of_stronglyMeasurable_left ((hSm n).const_mul 2) hprod (hint (n + 1))).trans ?_
      filter_upwards [increment_condExp μ X hX hindep hmean n] with ω hω
      simp [hω]

end H060

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `apply martingale_of_condExp_sub_eq_zero_nat` leaves three goals: adaptedness, integrability, and
    `μ[Sₙ₊₁ - Sₙ | ℱₙ] =ᵐ 0`. The increment of `S` is `X (n+1)`, which is independent of `ℱₙ`, so its
    conditional expectation is its mean `0`.
H2. Adapted: each `X i` with `i ≤ n` is ℱₙ-measurable (`stronglyAdapted_natural` + `.mono`, `StronglyMeasurable.mono`),
    then sum. Square walk: `|Sₙ| ≤ n + 1` gives integrability of `Sₙ`, `Sₙ²` (`Integrable.of_bound`); since
    `X² = 1` the increment is `2 Sₙ X (n+1)`; pull the known factor `2 Sₙ` out of the conditional expectation,
    and what remains is `μ[X (n+1) | ℱₙ] =ᵐ 0`.
H3. Increment: `condExp_indep_eq (hX (n+1)).measurable.comap_le (Filtration.le _ n)
      (comap_measurable (X (n+1))).stronglyMeasurable (hindep.indep_comap_natural_of_lt hX n.lt_succ_self)`,
    then `rw [hmean]`. Square: rewrite the increment as `(fun ω => 2 * S n ω) * X (n+1)` (`funext`,
    `Finset.sum_range_succ`, `linear_combination`), then
    `(condExp_mul_of_stronglyMeasurable_left ((hSm n).const_mul 2) hprod (hint (n+1))).trans ?_`
    and `filter_upwards [increment_condExp …]`.
-/
