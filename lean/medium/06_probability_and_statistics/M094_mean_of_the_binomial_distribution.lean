/- M094 | Mean of the binomial distribution | 15-20 min | binomial, integral_binomial, choose identities, binomial theorem, mathlib
GOAL
  The binomial law `Bin(n, p)` (successes in `n` independent coin flips with success probability `p`)
  has mean `n p`. Mathlib does not have this (it is only a `proof_wanted`): unfold the expectation into a
  finite sum and resum it with the binomial theorem.

REFERENCE
  `binomial n p : Measure ℕ` (notation `Bin(n, p)`), `p : unitInterval` (a real in `[0, 1]`, used as `(p : ℝ)`).
  `∫ k, (k : ℝ) ∂(binomial n p)` is `E[K]` for `K ~ Bin(n, p)`; `n.choose k` is the binomial coefficient.
  `•` is scalar multiplication, here ordinary `*` (`smul_eq_mul`).
  #check integral_binomial         -- ∫ x, f x ∂Bin(n, p) = ∑ k ∈ Iic n, (n.choose k * p ^ k * (1 - p) ^ (n - k)) • f k
  #check Nat.range_succ_eq_Iic     -- Finset.range (n + 1) = Finset.Iic n
  #check Finset.sum_range_succ'    -- ∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0
  #check Nat.add_one_mul_choose_eq -- (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)
  #check add_pow                   -- (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m
  #check Finset.mul_sum            -- (s f a) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
  #check Finset.sum_congr          -- s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g
  `exact_mod_cast h` moves a ℕ identity `h` into ℝ; `linear_combination e * h` closes a goal equal to `e * h` up to `ring`.
NOTE: `m + 1 - (k + 1)` is ℕ subtraction; rewrite it to `m - k` with `show … by omega` before using `ring`.
BANNED: bernsteinPolynomial
-/
import Mathlib

namespace M094

-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem binomial_mean (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) ∂(binomial n p) = n * p :=
-- END SPEC
  sorry

end M094

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. After `integral_binomial`, the goal is `∑ k ≤ n, C(n,k) p^k (1-p)^(n-k) k = n p`. The `k = 0` term
    vanishes, and `k C(n,k) = n C(n-1,k-1)` turns the rest into `n p` times a binomial expansion of `(p + (1 - p))^(n-1)`.
H2. `rw [integral_binomial, ← Nat.range_succ_eq_Iic]`, `cases n` (`zero` is `simp`), and for `m + 1` split off
    `k = 0` with `Finset.sum_range_succ'`. Prove termwise
    `C(m+1,k+1) p^(k+1) (1-p)^(m-k) (k+1) = (m+1) p (p^k (1-p)^(m-k) C(m,k))`, then `Finset.sum_congr`.
H3. The termwise step: cast `Nat.add_one_mul_choose_eq m k` to ℝ and `linear_combination p ^ (k + 1) * (1 - p) ^ (m - k) * h'.symm`;
    the end: `rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]`.
-/
