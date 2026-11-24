/- H090 | Gibbs variational principle | 1-1.5 h | free energy, entropy, log inequality, negMulLog, physlib
GOAL
  Units kB = 1, temperature `T = 1/b` with `b > 0`. For every probability distribution `p` on the
  microstates, the trial free energy `⟨E⟩_p - T S(p)` is at least `F = -T log Z`, where
  `⟨E⟩_p = ∑ i, p i * 𝓒.energy i` is the mean energy under `p`, the Gibbs entropy is
  `S(p) = ∑ i, negMulLog (p i)` and `negMulLog x = -x log x`. The Boltzmann distribution attains it.

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open CanonicalEnsemble Real

namespace H090

section Milestones

variable {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

/- SKELETON · sum_boltzmann   (milestone 1: ∑ q = 1; used in gibbs_inequality and gibbs_attained)
  1. One `simp only`: unfold `q i` under the sum, pull `/ Z b` out of it:   R1, R2 (right to left)
  2. The numerator is `Z b` by definition, so the goal is `Z b / Z b = 1`:   R5 with R3 → R4
-/
-- MILESTONE (optional: change or delete)
theorem sum_boltzmann (b : ℝ) : ∑ i, 𝓒.probabilityBetaReal b i = 1 := by
  sorry

/- SKELETON · log_boltzmann   (milestone 2: log q i = -b E i - log Z; used in gibbs_variational, gibbs_attained)
  1. Unfold `q i` (not under a binder, so `rw` works):                       R1
  2. Split the log of the quotient; side conditions `exp … ≠ 0`, `Z b ≠ 0`: R6 with (R7 → R4), (R3 → R4)
  3. Cancel `log (exp …)`:                                                   R8
  (2 and 3 fit in the same `rw [...]`.)
-/
-- MILESTONE (optional: change or delete)
theorem log_boltzmann (b : ℝ) (i : ι) :
    Real.log (𝓒.probabilityBetaReal b i) =
      -b * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) := by
  sorry

/- SKELETON · term_le   (milestone 3: the termwise bound; used in gibbs_inequality)
  1. Split `0 ≤ x` into `x = 0` and `0 < x` (bullets for the two goals):    R9
  2. Case `x = 0`: simplify, then the goal `0 ≤ y` follows from `hy`:       R10, R11
  3. Case `hx' : 0 < x`:
       h1 : log (y / x) ≤ y / x - 1                                         R12 with R13
       split `log (y / x)` inside h1 (pass `y ≠ 0`, `x ≠ 0` as arguments)  R14 (R4)
       h2 : multiply h1 by `x ≥ 0`                                          R15 with R16
       h3 : x * (y / x - 1) = y - x                                          R17
       combine h2, h3                                                        R11
-/
-- MILESTONE (optional: change or delete)
theorem term_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : x * (Real.log y - Real.log x) ≤ y - x := by
  sorry

/- SKELETON · gibbs_inequality   (milestone 4: ∑ p (log q - log p) ≤ 0; used in gibbs_variational)
  Uses milestones 1 and 3.
  1. hq : ∀ i, 0 < q i  (unfolds to `exp … / Z b` by definition):            R13 with R7, R3
  2. A two-step chain: `_ ≤ ∑ i, (q i - p i)`, then `_ = 0`:                  R18
  3. Step `≤`: termwise, each term is milestone 3 at `hp i`, `hq i`:          R19
  4. Step `= 0`: split the sum, then milestone 1, `hsum`, and `1 - 1`:        R20, rw [milestone 1, hsum], R21
-/
-- MILESTONE (optional: change or delete)
theorem gibbs_inequality (b : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, p i * (Real.log (𝓒.probabilityBetaReal b i) - Real.log (p i)) ≤ 0 := by
  sorry

end Milestones

/- SKELETON · gibbs_variational
  Prove the four milestones first; milestone 4 is the core, milestone 2 rewrites it.
  1. key : milestone 4 at `p`:                                                have
  2. Rewrite `log (q i)` inside `key`'s sum with milestone 2:                 R22
  3. Name `L := log Z`:                                                        R23
  4. Prove `expand : ∑ i, p i * (-b * E i - L - log (p i)) =
                     -b * ∑ i, p i * E i - L + ∑ i, negMulLog (p i)`:
       h1 : the left sum = ∑ i, (-b * (p i * E i) - L * p i + negMulLog (p i))
            (termwise; in each term unfold negMulLog, then `ring`)           R24, then R25 and `ring`
       rw [h1], split the sum, pull out `-b` and `L`, use `hsum`:            R26, R20, R27 (right to left) ×2, rw [hsum], R28
       (the same shape as W2 in guide.lean)
     then `rw [expand] at key`                                                R14
  5. Write the right side as `(b * ∑ i, p i * E i - ∑ i, negMulLog (p i)) / b`: R29 with R17
  6. Divide by `b`; the numerator inequality from `key`, and `0 ≤ b`:          R30 with R11, R16
-/
-- BEGIN SPEC
theorem gibbs_variational {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (hb : 0 < b) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    -Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) / b ≤
      ∑ i, p i * 𝓒.energy i - (∑ i, Real.negMulLog (p i)) / b :=
-- END SPEC
  sorry

/- SKELETON · gibbs_attained
  Uses milestones 1 and 2.
  1. Unfold `negMulLog` and rewrite `log (q i)` with milestone 2, one `simp only`: R25, R22 (on the goal)
  2. Prove `h : ∑ i, -q i * (-b * E i - log Z) = b * ∑ i, q i * E i + log Z * ∑ i, q i`:
       push `b` and `log Z` into the sums, merge them, compare termwise:      R27 ×2, R26 (right to left), R24 with `ring`
  3. rw [h, milestone 1]
  4. Clear the denominator `b`, then `ring`:                                   R17, ring
-/
-- BEGIN SPEC
theorem gibbs_attained {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (hb : 0 < b) :
    -Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) / b =
      ∑ i, 𝓒.probabilityBetaReal b i * 𝓒.energy i -
        (∑ i, Real.negMulLog (𝓒.probabilityBetaReal b i)) / b :=
-- END SPEC
  sorry

end H090

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `q i = 𝓒.probabilityBetaReal b i` for the Boltzmann weights. Since `log q i = -b E i - log Z`,
    multiplying the claim by `b > 0` turns it into Gibbs' inequality `∑ i, p i * (log (q i) - log (p i)) ≤ 0`
    (relative entropy ≥ 0). The four milestones are exactly these steps; prove them first.
H2. Milestones 1, 2: unfold `probabilityBetaReal` (R1); `← Finset.sum_div` and `div_self` (R2, R5);
    `Real.log_div` and `Real.log_exp` (R6, R8). Milestone 3: `rcases hx.eq_or_lt with rfl | hx'` (R9);
    if `0 < x`, `Real.log_le_sub_one_of_pos` at `y / x`, `Real.log_div … at h1`, then
    `mul_le_mul_of_nonneg_left` and `linarith` (R12–R15, R11). Milestone 4: `calc` with `Finset.sum_le_sum`,
    then `Finset.sum_sub_distrib`, `sum_boltzmann`, `hsum` (R18–R21).
    Main: `simp only [log_boltzmann] at key`, expand the sum termwise (`Finset.sum_congr rfl`,
    `Real.negMulLog`, `ring`), split and factor with `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`,
    `← Finset.mul_sum`, `hsum`, then divide by `b` (R22–R30).
H3. Milestone 4, step 1: `Finset.sum_le_sum fun i _ => term_le _ _ (hp i) (hq i)`.
    Final step of `gibbs_variational`: rewrite the right side as
    `(b * ∑ i, p i * 𝓒.energy i - ∑ i, negMulLog (p i)) / b` (`by field_simp`) and finish with
    `div_le_div_of_nonneg_right (by linarith) hb.le`. For `gibbs_attained`, `simp only [Real.negMulLog, log_boltzmann]`,
    turn the sum into `b * ∑ q E + log Z * ∑ q`, use `sum_boltzmann`, then `field_simp; ring`.
-/
