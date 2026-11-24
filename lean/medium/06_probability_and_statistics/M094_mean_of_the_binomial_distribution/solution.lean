/- M094 | Mean of the binomial distribution | 15-20 min | binomial, integral_binomial, choose identities, binomial theorem, mathlib
GOAL
  The binomial law `Bin(n, p)` (successes in `n` independent coin flips with success probability `p`)
  has mean `n p`. Mathlib does not have this (it is only a `proof_wanted`): unfold the expectation into a
  finite sum and resum it with the binomial theorem.
BANNED: bernsteinPolynomial

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M094

/- SKELETON · binomial_mean
  1. Integral → finite sum over `range (n + 1)`:                                  R1 → R2
  2. Split `n`:                                                                  R3
       zero:   one term, `k = 0`, worth 0:                                       simp
       succ m: steps 3–6
  3. Peel off the `k = 0` term and delete it (one `simp only` with both):        R4, then R5 + R6
  4. BEFORE resumming, prove the termwise identity for every `k ∈ range (m + 1)`:
       key : (summand of the goal, copied with its casts)
               = ↑(m + 1) * ↑p * (↑p ^ k * (1 - ↑p) ^ (m - k) * ↑(m.choose k))
     its proof:                                                                  have key … := by, R7
       a. absorption identity cast to ℝ:
            h' : ↑(m + 1) * ↑(m.choose k) = ↑((m + 1).choose (k + 1)) * ↑(k + 1)   R8 → R9
       b. `m + 1 - (k + 1)` → `m - k`:                                           R10
       c. close with a multiple of `h'.symm`:                                    R11
  5. Rewrite the sum with key, pull out `↑(m + 1) * ↑p`, collapse the
     binomial sum `∑ ↑p ^ k * (1 - ↑p) ^ (m - k) * ↑(m.choose k)`:              R12 → R13 → R14
  6. `↑p + (1 - ↑p)` → `1`, `1 ^ m` → `1`, `x * 1` → `x`:                         R15 → R16 → R17
-/
-- BEGIN SPEC
open MeasureTheory ProbabilityTheory

theorem binomial_mean (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) ∂(binomial n p) = n * p :=
-- END SPEC
  by
    rw [integral_binomial, ← Nat.range_succ_eq_Iic]
    cases n with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ']
      simp only [smul_eq_mul, Nat.cast_zero, mul_zero, add_zero]
      -- k C(m+1, k) = (m+1) C(m, k-1), shifted to k + 1
      have key : ∀ k ∈ Finset.range (m + 1),
          ((m + 1).choose (k + 1) * (p : ℝ) ^ (k + 1) * (1 - p) ^ (m + 1 - (k + 1))) * ((k + 1 : ℕ) : ℝ)
            = ((m + 1 : ℕ) : ℝ) * p * ((p : ℝ) ^ k * (1 - p) ^ (m - k) * (m.choose k)) := by
        intro k _
        have h' : ((m + 1 : ℕ) : ℝ) * (m.choose k) = ((m + 1).choose (k + 1)) * ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_one_mul_choose_eq m k
        -- WHY: ℕ subtraction; `ring` cannot see `m + 1 - (k + 1) = m - k`
        rw [show m + 1 - (k + 1) = m - k by omega]
        linear_combination (p : ℝ) ^ (k + 1) * (1 - p) ^ (m - k) * h'.symm
      rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]

end M094

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Bin(n, p)` lives on `{0, …, n}`, so the expectation is a finite sum (R1). From there it is the textbook
    proof: the `k = 0` term vanishes, `k C(n,k) = n C(n-1,k-1)` (R8, shifted to avoid ℕ subtraction), and what
    is left is `n p` times the binomial expansion of `(p + (1 - p))^(n-1)` (R14).
H2. `rw [integral_binomial, ← Nat.range_succ_eq_Iic]`, `cases n` (`zero` is `simp`); for `m + 1`,
    `rw [Finset.sum_range_succ']` and `simp only [smul_eq_mul, Nat.cast_zero, mul_zero, add_zero]`. Prove termwise
    `C(m+1,k+1) p^(k+1) (1-p)^(m+1-(k+1)) (k+1) = (m+1) p (p^k (1-p)^(m-k) C(m,k))` as `key`, then resum
    with `Finset.sum_congr rfl key`, `← Finset.mul_sum`, `← add_pow`.
H3. Inside `key`: `h' := by exact_mod_cast Nat.add_one_mul_choose_eq m k`, `rw [show m + 1 - (k + 1) = m - k by omega]`,
    `linear_combination (p : ℝ) ^ (k + 1) * (1 - p) ^ (m - k) * h'.symm`.
    The end: `rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]`.
-/
