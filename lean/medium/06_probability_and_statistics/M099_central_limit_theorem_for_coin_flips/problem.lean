/- M099 | Central limit theorem for coin flips | 10 min | CLT, HasLaw, gaussianReal, TendstoInDistribution, MemLp, mathlib
GOAL
  De Moivre–Laplace from Mathlib's CLT: i.i.d. 0/1 coin flips `X i` with mean `p` satisfy
  `(S_n - n p) / √n → N(0, p(1 - p))` in distribution, where `S_n = X 0 + … + X (n-1)` and the limit
  is any `Y` (on another space `Ω'`) whose law is the Gaussian `N(0, p(1 - p))`.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M099

open MeasureTheory ProbabilityTheory

/- SKELETON · clt_coin
  The CLT lemma (R10) proves this with `P[X 0]` for `p` and `Var[X 0; P]` for `p * (1 - p)`.
  Build its two missing inputs first (steps 1–4), then apply it and replace the mean (5–7).
  1. hb : ∀ᵐ ω ∂P, X 0 ω ∈ Set.Icc (0 : ℝ) 1
       a.e. from pointwise, as a term `… fun ω => by …`                     R1
       split `h01 0 ω`, simp each case                                       R2, R3
  2. hL2 : MemLp (X 0) 2 P          from hb and `hmeas 0`                     R4, R5
  3. hsq : X 0 ^ 2 = X 0
       function equation → one value, split `h01 0 ω`, simp each case     R6, R2, R7
  4. hvar : Var[X 0; P] = p * (1 - p)
       rewrite Var (needs hL2), then rw [hsq], rw [hp], then `ring`         R8
  5. hY in the form the CLT wants (`Var[X 0; P]` in place of `p * (1 - p)`)    R9 with hvar
  6. the CLT applied to step 5, hL2, hindep, hident, kept as `this`          R10
  7. `this` has `∫ x, X 0 x ∂P` where the goal has `p`: close with hp         R11
-/
-- BEGIN SPEC
theorem clt_coin {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P'] (X : ℕ → Ω → ℝ) (p : ℝ)
    (Y : Ω' → ℝ) (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hp : P[X 0] = p)
    (hY : HasLaw Y (gaussianReal 0 (p * (1 - p)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * p))
      Filter.atTop Y (fun _ => P) P' :=
-- END SPEC
  sorry

end M099

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The CLT lemma `tendstoInDistribution_inv_sqrt_mul_sum_sub` (R10) already has the right conclusion,
    with `P[X 0]` where you have `p`. You owe it two facts: `MemLp (X 0) 2 P`, and
    `Var[X 0; P] = p * (1 - p)` so that `hY` fits its first argument.
H2. `X 0` takes values in `[0, 1]`, so `memLp_of_bounded` (R4) gives square-integrability. Since
    `X 0 ^ 2 = X 0` as functions (values 0 or 1; `funext`, R6), `variance_eq_sub` (R8) gives `p - p ^ 2`.
H3. `have hvar : Var[X 0; P] = p * (1 - p) := by rw [variance_eq_sub hL2, hsq, hp]; ring`, then
    `have := tendstoInDistribution_inv_sqrt_mul_sum_sub (by rwa [hvar]) hL2 hindep hident` and `simpa [hp] using this`.
-/
