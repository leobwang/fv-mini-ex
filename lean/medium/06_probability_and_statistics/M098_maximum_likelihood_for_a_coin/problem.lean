/- M098 | Maximum likelihood for a coin | 15-20 min | log-likelihood, Gibbs inequality, casts, nlinarith, mathlib
GOAL
  A coin with heads-probability `θ` shows `k` heads in `n` flips (`0 < k < n`). Its log-likelihood
  `ℓ(θ) = k log θ + (n - k) log (1 - θ)` is maximised at the sample frequency `θ̂ = k / n`:
  `ℓ(θ) ≤ ℓ(k / n)` for every `θ ∈ (0, 1)`. Prove it without calculus, by Gibbs' inequality.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M098

-- BEGIN SPEC
/-- log-likelihood of `k` heads in `n` independent flips of a `θ`-coin (binomial factor dropped) -/
noncomputable def logLik (n k : ℕ) (θ : ℝ) : ℝ := k * Real.log θ + (n - k : ℕ) * Real.log (1 - θ)
-- END SPEC

/- SKELETON · mle_bernoulli      (write p for (k : ℝ) / n)
  1. Side facts first (MILESTONES; every later step uses them). State casts explicitly, `(0 : ℝ) < n`:
       hn    : (0 : ℝ) < n                     R1 with R2
       hk    : (0 : ℝ) < k                     R1
       hcast : ((n - k : ℕ) : ℝ) = n - k       R4 with R3   (used in step 5)
       hnk   : (0 : ℝ) < n - k                 R5, R1
       hp    : 0 < (k : ℝ) / n                 R6
       hq    : 0 < 1 - (k : ℝ) / n             R5, R7, R1
  2. The two Gibbs bounds, as hypotheses g1 (x = θ / p) and g2 (x = (1 - θ) / (1 - p)):
       positivity of x                         R9, and R10 for 0 < 1 - θ
       g : Real.log x ≤ x - 1                  R8
  3. Split the logs in g1 and g2:              R11 for the `≠ 0` arguments, R12 (`at g1`, `at g2`)
  4. Prove the identity (MILESTONE, used in step 5)
       e : k * (θ / p - 1) + (n - k) * ((1 - θ) / (1 - p) - 1) = 0
     with `0 < n - k` or `n - k ≠ 0` in context:           R13, then ring
  5. Unfold, remove the ℕ-subtraction cast, combine:
       R14 (unfold logLik), rw [hcast], R16 with the weighted bounds R15 (and R3) from g1, g2
-/
-- BEGIN SPEC
theorem mle_bernoulli (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    logLik n k θ ≤ logLik n k (k / n) :=
-- END SPEC
  sorry

end M098

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `p = k / n`. Then `ℓ(θ) - ℓ(p) = k log (θ / p) + (n - k) log ((1 - θ) / (1 - p))`, and the claim is
    that this is `≤ 0` (Gibbs' inequality: cross-entropy ≥ entropy). Bound each log with `log x ≤ x - 1`.
H2. First collect the side facts of SKELETON step 1 (positivity of `k`, `n - k`, `p`, `1 - p` in `ℝ`, and
    `hcast : ((n - k : ℕ) : ℝ) = n - k` by `Nat.cast_sub`). The weighted right-hand sides add up to exactly
    `0`, because `k / p = n` and `(n - k) / (1 - p) = n`: prove that identity `e` by `field_simp; ring`.
    The rest is a linear combination, once the bounds are multiplied by `k` and `n - k`.
H3. `have g1 := Real.log_le_sub_one_of_pos (div_pos h0 hp)`, then `rw [Real.log_div h0.ne' hp.ne'] at g1`;
    the same for `1 - θ` with `sub_pos.mpr h1` and `hq`. Finish with
    `unfold logLik; rw [hcast]; nlinarith [mul_le_mul_of_nonneg_left g1 hk.le, mul_le_mul_of_nonneg_left g2 hnk.le]`.
-/
