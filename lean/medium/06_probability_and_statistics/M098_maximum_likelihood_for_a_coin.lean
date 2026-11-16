/- M098 | Maximum likelihood for a coin | 15-20 min | log-likelihood, Gibbs inequality, casts, nlinarith, mathlib
GOAL
  A coin with heads-probability `θ` shows `k` heads in `n` flips (`0 < k < n`). Its log-likelihood
  `ℓ(θ) = k log θ + (n - k) log (1 - θ)` is maximised at the sample frequency `θ̂ = k / n`:
  `ℓ(θ) ≤ ℓ(k / n)` for every `θ ∈ (0, 1)`. Prove it without calculus, by Gibbs' inequality.

REFERENCE
  #check Real.log_le_sub_one_of_pos  -- 0 < x → Real.log x ≤ x - 1
  #check Real.log_div                -- x ≠ 0 → y ≠ 0 → Real.log (x / y) = Real.log x - Real.log y
  #check Nat.cast_sub                -- m ≤ n → ((n - m : ℕ) : R) = n - m
  #check div_lt_one                  -- 0 < b → (a / b < 1 ↔ a < b)
  example (k n : ℕ) (h : k < n) : (k : ℝ) < n := by exact_mod_cast h   -- move a fact across `↑`
  example (x y : ℝ) (hy : y ≠ 0) : x / y * y = x := by field_simp       -- clear denominators
  example (x y : ℝ) (h : x ≤ y) (c : ℝ) (hc : 0 ≤ c) : c * x ≤ c * y := mul_le_mul_of_nonneg_left h hc
  `nlinarith [h1, h2]` uses the listed facts (and their pairwise products) as extra hypotheses.
NOTE: `(n - k : ℕ)` is natural subtraction, then cast to ℝ; turn it into `(n : ℝ) - k` with `Nat.cast_sub`.
-/
import Mathlib

namespace M098

-- BEGIN SPEC
/-- log-likelihood of `k` heads in `n` independent flips of a `θ`-coin (binomial factor dropped) -/
noncomputable def logLik (n k : ℕ) (θ : ℝ) : ℝ := k * Real.log θ + (n - k : ℕ) * Real.log (1 - θ)
-- END SPEC

-- BEGIN SPEC
theorem mle_bernoulli (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    logLik n k θ ≤ logLik n k (k / n) :=
-- END SPEC
  sorry

end M098

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `p = k / n`. The claim is `k log (θ / p) + (n - k) log ((1 - θ) / (1 - p)) ≤ 0`
    (Gibbs' inequality: cross-entropy ≥ entropy).
H2. Bound each log with `log x ≤ x - 1`. After weighting by `k` and `n - k`, the right-hand sides
    add up to exactly `0`, because `k / p = n` and `(n - k) / (1 - p) = n`.
H3. First get `hk : (0:ℝ) < k`, `hnk : (0:ℝ) < n - k`, `hp : 0 < (k:ℝ) / n`, `hq : 0 < 1 - (k:ℝ) / n`
    (`exact_mod_cast`, `positivity`, `div_lt_one`) and `hcast : ((n - k : ℕ) : ℝ) = n - k`.
    `have g1 := Real.log_le_sub_one_of_pos (div_pos h0 hp)` then `rw [Real.log_div ..] at g1` (same for
    `1 - θ`); prove `k * (θ / p - 1) + (n - k) * ((1 - θ) / (1 - p) - 1) = 0` by `field_simp; ring`;
    `unfold logLik; rw [hcast]; nlinarith [mul_le_mul_of_nonneg_left g1 hk.le, mul_le_mul_of_nonneg_left g2 hnk.le]`.
-/
