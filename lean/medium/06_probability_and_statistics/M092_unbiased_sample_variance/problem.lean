/- M092 | Unbiased sample variance | 15-20 min | sample variance, variance_eq_sub, IndepFun.variance_sum, Finset sums, mathlib
GOAL
  For pairwise independent `X 0, …, X (n-1)` (`n ≥ 2`) with common mean `m` and common variance `σ2`, the
  sample variance `S² = (∑ i < n, (X i - X̄)²) / (n - 1)`, where `X̄ = (∑ i < n, X i) / n` is the sample
  mean, is unbiased: `E[S²] = σ2`. (Dividing by `n - 1`, not `n`, is what makes it unbiased.)

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M092

/- SKELETON · sample_var_unbiased
  `μ[F]` is the expectation ∫ F dμ; the infoview prints it as `∫ (x : Ω), F x ∂μ`.
  Prove these milestones as `have`s, in this order, then the main goal (step 7).
  1. Facts about n:
       hn0 : 0 < n                                                          R1
       hn' : (n : ℝ) ≠ 0                                                    R2
       hn1 : (n : ℝ) - 1 ≠ 0       first (1 : ℝ) < n, then                  R3 → R4
  2. Milestone `key`, plain algebra for every x : ℕ → ℝ (used in step 4):
       ∑ i ∈ range n, (x i - (∑ j ∈ range n, x j) / n) ^ 2
         = ∑ i ∈ range n, x i ^ 2 - (∑ i ∈ range n, x i) ^ 2 / n
       intro x, then one `simp only` with                                   R5, R6, R7, R8, R9, R10
       clear the `/ n` (uses hn'), then close                               R11 → R12
  3. Name the sum S := ∑ i ∈ range n, X i, a function Ω → ℝ:                 R13
       hSL2 : MemLp S 2 μ                                                   R14
       hSapp : ∀ ω, S ω = ∑ i ∈ range n, X i ω
         intro ω, then one `simp only` with hS and                          R15
         (`S` is a local definition: R15 alone cannot see inside it)
  4. Milestone `e` (used in step 7):
       sampleVar n X = fun ω => (∑ i ∈ range n, X i ω ^ 2 - S ω ^ 2 / n) / ((n : ℝ) - 1)
       R16, then `simp only` with sampleVar, sampleMean, hSapp, then rw [key]
  5. Milestone `hsq : ∀ i, μ[fun ω => X i ω ^ 2] = σ2 + m ^ 2` (used in step 7):
       R17 on hL2 i → R18 with hvar, hmean → R19 → R4
  6. Milestone `hS2 : μ[fun ω => S ω ^ 2] = n * σ2 + (n * m) ^ 2` (used in step 7). First:
       hSmean : μ[S] = n * m
         `simp only` with hS and R15 → R20 (its argument by R21) → `simp only` with hmean, R10
       hSvar  : Var[S; μ] = n * σ2
         rw [hS] → R22 (its pairwise argument by R23) → `simp only` with hvar, R10
     then as in step 5: R17 on hSL2 → R18 with hSvar, hSmean → R19 → R4
  7. Main goal: rw [e], R24, R25, R20, R24, rw [hS2]. Four goals remain, in order:
       the number: `simp only` with hsq and the R10 lemmas, then              R11 → R12
       ∀ i ∈ range n, Integrable (fun a => X i a ^ 2) μ                     R26
       Integrable (fun a => ∑ i ∈ range n, X i a ^ 2) μ                    R27 with R26
       Integrable (fun a => S a ^ 2 / n) μ                                  R26, R28
-/
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
  sorry

end M092

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `S` for `∑ i ∈ range n, X i`. Pointwise, `∑ (X i - X̄)² = ∑ X i ² - S² / n` (milestone `key`,
    plain algebra). So you need only `E[X i ²] = σ2 + m²` and `E[S²] = Var S + E[S]² = n σ2 + (n m)²`,
    both from `variance_eq_sub` (R17). Independence enters only in `Var S = n σ2` (R22).
H2. Follow the SKELETON: facts about `n`; `key` by expanding the squares and pulling constants out of
    the sums; `set S`; `e : sampleVar n X = fun ω => (∑ i ∈ range n, X i ω ^ 2 - S ω ^ 2 / n) / (n - 1)`
    by `funext` and `key`; the second moments `hsq`, `hS2` from `variance_eq_sub` and `linarith`;
    `E[S] = n m` by `integral_finsetSum`; `Var S = n σ2` by `IndepFun.variance_sum`. Then rewrite the
    goal with `e` and push the integral through `/`, `-` and `∑`.
H3. `key`: `simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`, then `field_simp` and `ring`.
    `hSvar`: `rw [hS, IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)]`.
    Main: `rw [e, integral_div, integral_sub, integral_finsetSum, integral_div, hS2]`; the side goals by
    `(hL2 i).integrable_sq`, `integrable_finsetSum`, `hSL2.integrable_sq.div_const _`.
-/
