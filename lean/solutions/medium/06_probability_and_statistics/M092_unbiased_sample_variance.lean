/- M092 | Unbiased sample variance | 15-20 min | sample variance, variance_eq_sub, IndepFun.variance_sum, Finset sums, mathlib
GOAL
  For pairwise independent `X 0, …, X (n-1)` (`n ≥ 2`) with common mean `m` and common variance `σ2`, the
  sample variance `S² = (∑ i < n, (X i - X̄)²) / (n - 1)`, where `X̄ = (∑ i < n, X i) / n` is the sample
  mean, is unbiased: `E[S²] = σ2`. (Dividing by `n - 1`, not `n`, is what makes it unbiased.)

REFERENCE
  `μ[F]` is `E[F] = ∫ ω, F ω ∂μ`; `Var[X; μ]` is the variance; `MemLp X 2 μ`: `E[X²] < ∞`; `X ⟂ᵢ[μ] Y`: independent.
  `Pairwise fun i j => X i ⟂ᵢ[μ] X j`: distinct `X i`, `X j` are independent (`hindep hij`, `hij : i ≠ j`).
  #check variance_eq_sub       -- MemLp X 2 μ → Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2      (`Pi.pow_apply` unfolds `X ^ 2`)
  #check IndepFun.variance_sum -- (∀ i ∈ s, MemLp (X i) 2 μ) → (↑s).Pairwise (fun i j => X i ⟂ᵢ[μ] X j) → Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, Var[X i; μ]
  #check memLp_finsetSum'      -- (s) : (∀ i ∈ s, MemLp (f i) p μ) → MemLp (∑ i ∈ s, f i) p μ
  #check integral_finsetSum    -- (s) : (∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ
  #check integrable_finsetSum  -- (s) : (∀ i ∈ s, Integrable (f i) μ) → Integrable (fun a => ∑ i ∈ s, f i a) μ
  #check integral_sub          -- Integrable f μ → Integrable g μ → ∫ a, f a - g a ∂μ = ∫ f - ∫ g;  also `integral_div`
  #check Finset.sum_apply      -- (∑ c ∈ s, g c) a = ∑ c ∈ s, g c a      (a sum of functions, applied)
  #check sub_sq                -- (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2;  with `Finset.sum_sub_distrib`, `Finset.sum_mul`
NOTE: `∑ i ∈ range n, c` simplifies to `n • c` (`Finset.sum_const`, `Finset.card_range`); `nsmul_eq_mul` makes it `n * c`.
-/
import Mathlib

namespace M092

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

/-- The sample mean `X̄ = (X 0 + … + X (n-1)) / n`, at the outcome `ω`. -/
noncomputable def sampleMean {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / n

/-- The sample variance `S² = ((X 0 - X̄)² + … + (X (n-1) - X̄)²) / (n - 1)`. -/
noncomputable def sampleVar {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, (X i ω - sampleMean n X ω) ^ 2) / ((n : ℝ) - 1)

theorem sample_var_unbiased {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 < n) (X : ℕ → Ω → ℝ) (m σ2 : ℝ)
    (hL2 : ∀ i, MemLp (X i) 2 μ) (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m) (hvar : ∀ i, Var[X i; μ] = σ2) :
    μ[sampleVar n X] = σ2 :=
-- END SPEC
  by
    have hn0 : 0 < n := by omega
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < n := by exact_mod_cast hn
      linarith
    -- the algebra: ∑ (x i - x̄)² = ∑ x i ² - (∑ x i)² / n
    have key : ∀ x : ℕ → ℝ, ∑ i ∈ Finset.range n, (x i - (∑ j ∈ Finset.range n, x j) / n) ^ 2
        = ∑ i ∈ Finset.range n, x i ^ 2 - (∑ i ∈ Finset.range n, x i) ^ 2 / n := by
      intro x
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring
    set S : Ω → ℝ := ∑ i ∈ Finset.range n, X i with hS
    have hSL2 : MemLp S 2 μ := memLp_finsetSum' _ (fun i _ => hL2 i)
    have hSapp : ∀ ω, S ω = ∑ i ∈ Finset.range n, X i ω := fun ω => by simp [hS, Finset.sum_apply]
    have e : sampleVar n X
        = fun ω => (∑ i ∈ Finset.range n, X i ω ^ 2 - S ω ^ 2 / n) / ((n : ℝ) - 1) := by
      funext ω; simp only [sampleVar, sampleMean, hSapp]; rw [key]
    -- second moments from `Var Z = E[Z²] - E[Z]²`
    have hsq : ∀ i, μ[fun ω => X i ω ^ 2] = σ2 + m ^ 2 := by
      intro i
      have := variance_eq_sub (hL2 i)
      rw [hvar, hmean] at this
      simp only [Pi.pow_apply] at this
      linarith
    have hSmean : μ[S] = n * m := by
      simp only [hS, Finset.sum_apply]
      rw [integral_finsetSum _ (fun i _ => (hL2 i).integrable one_le_two)]
      simp [hmean]
    -- independence enters only here
    have hSvar : Var[S; μ] = n * σ2 := by
      rw [hS, IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]
      simp [hvar]
    have hS2 : μ[fun ω => S ω ^ 2] = n * σ2 + (n * m) ^ 2 := by
      have := variance_eq_sub hSL2
      rw [hSvar, hSmean] at this
      simp only [Pi.pow_apply] at this
      linarith
    rw [e, integral_div, integral_sub, integral_finsetSum, integral_div, hS2]
    · simp only [hsq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring
    · exact fun i _ => (hL2 i).integrable_sq
    · exact integrable_finsetSum _ (fun i _ => (hL2 i).integrable_sq)
    · exact hSL2.integrable_sq.div_const _

end M092

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `S` for `∑ i ∈ range n, X i`. Pointwise, `∑ (X i - X̄)² = ∑ X i ² - S² / n`. Then you need only
    `E[X i ²] = σ2 + m²` and `E[S²] = Var S + E[S]² = n σ2 + (n m)²`, both from `variance_eq_sub`.
H2. Prove the algebra first, for plain reals: `∑ i ∈ range n, (x i - (∑ j ∈ range n, x j) / n) ^ 2
    = ∑ i ∈ range n, x i ^ 2 - (∑ i ∈ range n, x i) ^ 2 / n` (needs `(n : ℝ) ≠ 0`). Use it to rewrite
    `sampleVar n X` as `fun ω => (∑ i ∈ range n, X i ω ^ 2 - S ω ^ 2 / n) / ((n : ℝ) - 1)` (`funext ω`,
    `simp only [sampleVar, sampleMean, Finset.sum_apply]`). `E[S] = n m` by `integral_finsetSum`;
    `Var S = n σ2` by `IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)`.
H3. Algebra: `simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]`, then `field_simp` and `ring`. Main:
    `rw [e, integral_div, integral_sub, integral_finsetSum, integral_div, hS2]`, close the side goals with
    `(hL2 i).integrable_sq`, `integrable_finsetSum`, `hSL2.integrable_sq.div_const _`, and finish with `simp only [hsq, …]; field_simp; ring`.
-/
