/- H053 | Variance of the binomial distribution | 1-1.5 h | binomial, factorial moments, variance_eq_sub, choose identities, binomial theorem, mathlib
GOAL
  `binomial n p : Measure ℕ` (notation `Bin(n, p)`, `p : unitInterval` = a real in [0, 1]) is the
  law of the number of successes in `n` independent `p`-coin flips. Prove `Var = n p (1 - p)`
  (Mathlib only has this as `proof_wanted`). `Var[X; μ]` is the variance of `X : ℕ → ℝ` under `μ`.

REFERENCE
  #check integral_binomial  -- ∫ x, f x ∂Bin(n, p) = ∑ k ∈ Finset.Iic n, (n.choose k * p ^ k * (1 - p) ^ (n - k)) • f k
  #check smul_eq_mul  -- a • b = a * b   (`•` is scalar multiplication; on ℝ it is just `*`)
  #check integrable_binomial  -- (f : ℕ → E) : Integrable f Bin(n, p)   (every f; finite support)
  #check variance_eq_sub  -- MemLp X 2 μ → Var[X; μ] = ∫ x, (X ^ 2) x ∂μ - (∫ x, X x ∂μ) ^ 2
  #check Pi.pow_apply  -- (f ^ a) i = f i ^ a   (turns `(X ^ 2) x` into `X x ^ 2`)
  #check memLp_two_iff_integrable_sq  -- AEStronglyMeasurable f μ → (MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ)
  #check integral_add  -- Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
  #check Nat.add_one_mul_choose_eq  -- (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)
  #check add_pow  -- (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m
  #check Finset.sum_range_succ'  -- ∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0
  example (n : ℕ) : Finset.range (n + 1) = Finset.Iic n := Nat.range_succ_eq_Iic n
  -- `match n with | 0 => .. | 1 => .. | m + 2 => ..`;  `linear_combination e₁ * h₁ + e₂ * h₂`
NOTE: `MemLp X 2 μ`: `X` is a.e.-strongly measurable and `∫ |X|² ∂μ < ∞` (`X ∈ L²(μ)`).
  The mean milestone `binomial_mean` is problem M094; its proof is H2's pattern with one peeled term.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H053

-- MILESTONE (optional: change or delete)
/-- The mean `E[K] = n p` (problem M094). -/
theorem binomial_mean (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) ∂(binomial n p) = n * p := by
  sorry

-- MILESTONE (optional: change or delete)
/-- The second factorial moment `E[K (K - 1)] = n (n - 1) p²`. -/
theorem binomial_factorial_moment (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) * ((k : ℝ) - 1) ∂(binomial n p) = n * (n - 1) * (p : ℝ) ^ 2 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- `E[K²] = E[K (K - 1)] + E[K]`. -/
theorem binomial_second_moment (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) ^ 2 ∂(binomial n p) =
      ∫ k, (k : ℝ) * ((k : ℝ) - 1) ∂(binomial n p) + ∫ k, (k : ℝ) ∂(binomial n p) := by
  sorry

-- BEGIN SPEC
theorem binomial_variance (n : ℕ) (p : unitInterval) :
    Var[fun k : ℕ => (k : ℝ); binomial n p] = n * p * (1 - p) :=
-- END SPEC
  sorry

end H053

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Var = E[K²] - E[K]²` and `E[K²] = E[K(K-1)] + E[K]`; the factorial moment `E[K(K-1)]` is the
    only real computation. Every function is integrable against `Bin(n, p)`.
H2. Factorial moment: `rw [integral_binomial, ← Nat.range_succ_eq_Iic]`, split `n = 0 | 1 | m + 2`;
    for `m + 2` peel the `k = 0, 1` terms with `Finset.sum_range_succ'` twice (they vanish), rewrite each
    remaining term as `(m+2)(m+1) p² · (p^k (1-p)^(m-k) C(m,k))`, pull the constant out, and use `add_pow`
    backwards: `∑ p^k (1-p)^(m-k) C(m,k) = (p + (1 - p))^m = 1`.
H3. Per-term identity `(k+2)(k+1) C(m+2,k+2) = (m+2)(m+1) C(m,k)` from `Nat.add_one_mul_choose_eq m k` and
    `Nat.add_one_mul_choose_eq (m+1) (k+1)` (cast with `exact_mod_cast`), then `linear_combination`;
    finish with `rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]`.
    Main: `MemLp` via `(memLp_two_iff_integrable_sq (integrable_binomial _).aestronglyMeasurable).2
    (integrable_binomial _)`, then `rw [variance_eq_sub hL2]; simp only [Pi.pow_apply]` (this turns
    `(X ^ 2) x` into `x ^ 2`), then `rw [binomial_second_moment, binomial_factorial_moment, binomial_mean]; ring`.
-/
