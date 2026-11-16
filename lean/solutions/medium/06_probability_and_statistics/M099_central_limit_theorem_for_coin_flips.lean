/- M099 | Central limit theorem for coin flips | 10 min | CLT, HasLaw, gaussianReal, TendstoInDistribution, MemLp, mathlib
GOAL
  De Moivre–Laplace from Mathlib's CLT: i.i.d. 0/1 coin flips `X i` with mean `p` satisfy
  `(S_n - n p) / √n → N(0, p(1 - p))` in distribution, where `S_n = X 0 + … + X (n-1)` and the limit
  is any `Y` (on another space `Ω'`) whose law is the Gaussian `N(0, p(1 - p))`.

REFERENCE
  #check @tendstoInDistribution_inv_sqrt_mul_sum_sub  -- the CLT; its first argument is
    -- HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P'; then MemLp (X 0) 2 P, iIndepFun X P, ident. distrib.
  #check memLp_of_bounded   -- (∀ᵐ x ∂μ, f x ∈ Set.Icc a b) → AEStronglyMeasurable f μ → ∀ p, MemLp f p μ
  #check variance_eq_sub    -- MemLp X 2 μ → Var[X; μ] = ∫ x, (X ^ 2) x ∂μ - (∫ x, X x ∂μ) ^ 2
  #check @Measurable.aestronglyMeasurable
  example (P : Measure ℝ) : ∀ᵐ x ∂P, x ^ 2 ≥ 0 := Filter.Eventually.of_forall fun x => by positivity
  `P[f]` = `∫ ω, f ω ∂P` (expectation); `HasLaw Y μ P'`: the law of `Y` under `P'` is `μ`.
  `gaussianReal m v` = N(m, v) with `v : ℝ≥0`; `x.toNNReal` = `max x 0` as an `ℝ≥0`.
  `Var[X; P]` = variance of `X` under `P`, i.e. `∫ (X - P[X])^2 ∂P`.
  `MemLp f 2 P`: `f` is square-integrable. `simpa [h] using t` rewrites `t` and the goal, then closes.
NOTE: `X 0 ^ 2 = X 0` pointwise (values are 0 or 1), so `variance_eq_sub` gives `p - p ^ 2`.
-/
import Mathlib

namespace M099

open MeasureTheory ProbabilityTheory

-- BEGIN SPEC
theorem clt_coin {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P'] (X : ℕ → Ω → ℝ) (p : ℝ)
    (Y : Ω' → ℝ) (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hp : P[X 0] = p)
    (hY : HasLaw Y (gaussianReal 0 (p * (1 - p)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * p))
      Filter.atTop Y (fun _ => P) P' :=
-- END SPEC
  by
    have hb : ∀ᵐ ω ∂P, X 0 ω ∈ Set.Icc (0 : ℝ) 1 := Filter.Eventually.of_forall fun ω => by
      rcases h01 0 ω with h | h <;> simp [h]
    have hL2 : MemLp (X 0) 2 P := memLp_of_bounded hb (hmeas 0).aestronglyMeasurable 2
    have hsq : X 0 ^ 2 = X 0 := by
      funext ω; rcases h01 0 ω with h | h <;> simp [h]
    have hvar : Var[X 0; P] = p * (1 - p) := by
      rw [variance_eq_sub hL2, hsq, hp]; ring
    have := tendstoInDistribution_inv_sqrt_mul_sum_sub (by rwa [hvar]) hL2 hindep hident
    simpa [hp] using this

end M099

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The CLT lemma already has the right conclusion, with `P[X 0]` where you have `p`. You owe it
    two facts: `MemLp (X 0) 2 P`, and `Var[X 0; P] = p * (1 - p)` so that `hY` fits its first argument.
H2. `X 0` takes values in `[0, 1]`, so `memLp_of_bounded` gives square-integrability. Since
    `X 0 ^ 2 = X 0` pointwise, `variance_eq_sub` gives `p - p ^ 2`.
H3. `have hvar : Var[X 0; P] = p * (1 - p) := by rw [variance_eq_sub hL2, hsq, hp]; ring`, then
    `have := tendstoInDistribution_inv_sqrt_mul_sum_sub (by rwa [hvar]) hL2 hindep hident` and `simpa [hp] using this`.
-/
