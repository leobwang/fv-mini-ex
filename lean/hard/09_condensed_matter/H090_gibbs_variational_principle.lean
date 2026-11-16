/- H090 | Gibbs variational principle | 1-1.5 h | free energy, entropy, log inequality, negMulLog, physlib
GOAL
  Units kB = 1, temperature `T = 1/b` with `b > 0`. For every probability distribution `p` on the
  microstates, the trial free energy `⟨E⟩_p - T S(p)` is at least `F = -T log Z`, where
  `⟨E⟩_p = ∑ i, p i * 𝓒.energy i` is the mean energy under `p`, the Gibbs entropy is
  `S(p) = ∑ i, negMulLog (p i)` and `negMulLog x = -x log x`. The Boltzmann distribution attains it.

REFERENCE
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal  -- Z(b) = ∑ i, exp (-b * 𝓒.energy i)
  #check CanonicalEnsemble.probabilityBetaReal  -- p b i = exp (-b * 𝓒.energy i) / Z(b)
  #check CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos  -- [Nonempty ι] : 0 < Z(b)
  #check Real.negMulLog            -- negMulLog x = -x * log x   (unfold with `simp only [Real.negMulLog]`)
  #check Real.log_le_sub_one_of_pos  -- 0 < x → log x ≤ x - 1
  #check Real.log_div              -- x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y
  #check Real.log_exp              -- log (exp x) = x
  #check Finset.sum_le_sum         -- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
  #check div_le_div_of_nonneg_right  -- a ≤ b → 0 ≤ c → a / c ≤ b / c
  example (x : ℝ) (h : 0 ≤ x) : x = 0 ∨ 0 < x := h.eq_or_lt.imp Eq.symm id   -- or `rcases h.eq_or_lt with rfl | h'`
  Note `log 0 = 0` in Mathlib, so `0 * log 0 = 0`: zero-probability states drop out on their own.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open CanonicalEnsemble Real

namespace H090

section Milestones

variable {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

-- MILESTONE (optional: change or delete)
theorem sum_boltzmann (b : ℝ) : ∑ i, 𝓒.probabilityBetaReal b i = 1 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem log_boltzmann (b : ℝ) (i : ι) :
    Real.log (𝓒.probabilityBetaReal b i) =
      -b * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem term_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : x * (Real.log y - Real.log x) ≤ y - x := by
  sorry

-- MILESTONE (optional: change or delete)
theorem gibbs_inequality (b : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, p i * (Real.log (𝓒.probabilityBetaReal b i) - Real.log (p i)) ≤ 0 := by
  sorry

end Milestones

-- BEGIN SPEC
theorem gibbs_variational {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (𝓒 : CanonicalEnsemble ι) (b : ℝ) (hb : 0 < b) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    -Real.log (𝓒.mathematicalPartitionFunctionBetaReal b) / b ≤
      ∑ i, p i * 𝓒.energy i - (∑ i, Real.negMulLog (p i)) / b :=
-- END SPEC
  sorry

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
H1. Write `q i = p b i` for the Boltzmann weights. Since `log q i = -b E i - log Z`, multiplying the claim by
    `b > 0` turns it into Gibbs' inequality `∑ i, p i * (log (q i) - log (p i)) ≤ 0` (relative entropy ≥ 0).
H2. Termwise `p (log q - log p) ≤ q - p`: if `p = 0` both sides are trivial; otherwise apply
    `Real.log_le_sub_one_of_pos` to `q / p` and multiply by `p`. Summing gives `≤ ∑ q - ∑ p = 1 - 1 = 0`.
    Then rewrite `log q i` with `log_boltzmann`, expand `∑ p (-b E - log Z - log p)` using `∑ p = 1`,
    and divide by `b`.
H3. Final step of `gibbs_variational`: rewrite the right side as
    `(b * ∑ i, p i * 𝓒.energy i - ∑ i, negMulLog (p i)) / b` (`by field_simp`) and finish with
    `div_le_div_of_nonneg_right (by linarith) hb.le`. For `gibbs_attained`, `simp only [Real.negMulLog, log_boltzmann]`,
    turn the sum into `b * ∑ q E + log Z * ∑ q`, use `sum_boltzmann`, then `field_simp; ring`.
-/
