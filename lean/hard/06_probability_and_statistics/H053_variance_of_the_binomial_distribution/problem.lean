/- H053 | Variance of the binomial distribution | 1-1.5 h | binomial, factorial moments, variance_eq_sub, choose identities, binomial theorem, mathlib
GOAL
  `binomial n p : Measure ℕ` (notation `Bin(n, p)`, `p : unitInterval` = a real in [0, 1]) is the
  law of the number of successes in `n` independent `p`-coin flips. Prove `Var = n p (1 - p)`
  (Mathlib only has this as `proof_wanted`). `Var[X; μ]` is the variance of `X : ℕ → ℝ` under `μ`.

GUIDE
  Entries R1–R27: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H053

/- SKELETON · binomial_mean   (milestone 1; M094 proves it: paste your proof)
  1. Integral → sum over `Finset.range (n + 1)`:                             R1, R2
  2. Split n = 0 | m + 1 (`cases n with | zero => … | succ m => …`, like R3):
       zero: the sum has one term, 0:                                        simp
  3. succ m: peel the k = 0 term (its factor ↑0 kills it), clean up:         R4, then R6, R7, R8
  4. Per-term identity, for every k (R9):
       key : ∀ k ∈ range (m + 1),
               C(m+1, k+1) · p^(k+1) · (1-p)^(m+1-(k+1)) · ↑(k+1)
                 = ↑(m+1) · p · (p^k · (1-p)^(m-k) · C(m, k))
       h : (m+1)·C(m,k) = C(m+1,k+1)·(k+1), in ℝ                            R10 → R11
       exponent m + 1 - (k + 1) → m - k                                     R12
       close from h (coefficient p^(k+1) · (1-p)^(m-k), h reversed)          R14
  5. Rewrite every term, pull out ↑(m+1) · p, fold the binomial theorem,
     p + (1 - p) = 1, 1 ^ m = 1, · 1:                                       R15 → R16 → R17 → R18 → R19
-/
-- MILESTONE (optional: change or delete)
/-- The mean `E[K] = n p` (problem M094). -/
theorem binomial_mean (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) ∂(binomial n p) = n * p := by
  sorry

/- SKELETON · binomial_factorial_moment   (milestone 2: the only real computation)
  1. Integral → sum over `Finset.range (n + 1)`:                             R1, R2
  2. Split n = 0 | 1 | m + 2:                                                R3
       0: one term, 0:                                                       simp
       1: unroll the two-term sum:                                           simp with R5
  3. m + 2: peel the k = 0 and k = 1 terms (factor k (k - 1) = 0), clean up: R4 twice, then R6, R7, R8
  4. Per-term identity, for every k (R9):
       key : ∀ k ∈ range (m + 1),
               C(m+2, k+2) · p^(k+2) · (1-p)^(m+2-(k+2)) · (↑(k+2) · (↑(k+2) - 1))
                 = ↑(m+2) · (↑(m+2) - 1) · p² · (p^k · (1-p)^(m-k) · C(m, k))
       h1 : absorption at (m, k), in ℝ                                      R10 → R11
       h2 : absorption at (m + 1, k + 1), in ℝ                              R10 → R11
       exponent m + 2 - (k + 1 + 1) → m - k                                 R12
       push the casts in h1, h2 and the goal                                R13
       close from h1, h2: coefficient p^(k+2) · (1-p)^(m-k) times a
       combination of h2.symm (weight k + 1) and h1.symm (weight m + 2)      R14
  5. As in milestone 1:                                                     R15 → R16 → R17 → R18 → R19
-/
-- MILESTONE (optional: change or delete)
/-- The second factorial moment `E[K (K - 1)] = n (n - 1) p²`. -/
theorem binomial_factorial_moment (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) * ((k : ℝ) - 1) ∂(binomial n p) = n * (n - 1) * (p : ℝ) ^ 2 := by
  sorry

/- SKELETON · binomial_second_moment   (milestone 3)
  1. Merge the two integrals on the right (both integrands integrable):     R20, R21
  2. Integrals equal ← integrands equal, pointwise:                          R22 → R23
  3. ↑k ^ 2 = ↑k * (↑k - 1) + ↑k:                                            ring
-/
-- MILESTONE (optional: change or delete)
/-- `E[K²] = E[K (K - 1)] + E[K]`. -/
theorem binomial_second_moment (n : ℕ) (p : unitInterval) :
    ∫ k, (k : ℝ) ^ 2 ∂(binomial n p) =
      ∫ k, (k : ℝ) * ((k : ℝ) - 1) ∂(binomial n p) + ∫ k, (k : ℝ) ∂(binomial n p) := by
  sorry

/- SKELETON · binomial_variance
  Prove the three milestones first: binomial_mean (M094), binomial_factorial_moment,
  binomial_second_moment. All three are used in step 4.
  1. hL2 : MemLp (fun k : ℕ => (k : ℝ)) 2 (binomial n p)
       measurability from integrability, then the `.2` of the L² criterion,
       the square integrable too:                                            R20, R24, R25
  2. Var → E[K²] - E[K]²:                                                    R26
  3. ((fun k => ↑k) ^ 2) x → ↑x ^ 2:                                         R27
  4. rewrite E[K²] (milestone 3), then E[K(K-1)] (milestone 2), E[K] (milestone 1):  rw [h]
  5. n (n - 1) p² + n p - (n p)² = n p (1 - p):                              ring
-/
-- BEGIN SPEC
theorem binomial_variance (n : ℕ) (p : unitInterval) :
    Var[fun k : ℕ => (k : ℝ); binomial n p] = n * p * (1 - p) :=
-- END SPEC
  sorry

end H053

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Var = E[K²] - E[K]²` (R26; it needs `K ∈ L²`, R25) and `E[K²] = E[K(K-1)] + E[K]` (linearity,
    R21). The factorial moment `E[K(K-1)] = n(n-1)p²` is the only real computation; `E[K] = np` is
    M094. Every function `ℕ → ℝ` is integrable against `Bin(n, p)` (R20).
H2. Factorial moment: `rw [integral_binomial, ← Nat.range_succ_eq_Iic]`, split `n = 0 | 1 | m + 2`; for
    `m + 2` peel the `k = 0, 1` terms with `Finset.sum_range_succ'` twice (they vanish), rewrite each
    remaining term as `(m+2)(m+1) p² · (p^k (1-p)^(m-k) C(m,k))` (`Finset.sum_congr`), pull the constant
    out (`← Finset.mul_sum`) and use `add_pow` backwards: `∑ p^k (1-p)^(m-k) C(m,k) = (p + (1 - p))^m = 1`.
H3. Per-term identity `(k+2)(k+1) C(m+2,k+2) = (m+2)(m+1) C(m,k)` from `Nat.add_one_mul_choose_eq m k` and
    `Nat.add_one_mul_choose_eq (m+1) (k+1)` (cast with `exact_mod_cast`), then `push_cast at h1 h2 ⊢` and
    `linear_combination`; finish with
    `rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]`.
    Main: `MemLp` via `(memLp_two_iff_integrable_sq (integrable_binomial _).aestronglyMeasurable).2
    (integrable_binomial _)`, then `rw [variance_eq_sub hL2]; simp only [Pi.pow_apply]`, then
    `rw [binomial_second_moment, binomial_factorial_moment, binomial_mean]; ring`.
-/
