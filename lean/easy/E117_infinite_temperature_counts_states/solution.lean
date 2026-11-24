/- E117 | Infinite temperature counts states | 2-3 min | mathematicalPartitionFunctionBetaReal, Finset.sum_const, simp, physlib
GOAL
  `𝓒.mathematicalPartitionFunctionBetaReal b` is `Z(β) = ∑ i, e^{-β E_i}` over the finitely many states
  `i : ι` (units with k_B = 1, β a plain real). If every state has energy `E`, `Z = |ι| e^{-βE}`; and at
  `β = 0` (infinite temperature) every weight is 1, so `Z` counts the states.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble

namespace E117

/- SKELETON · Z_degenerate
  1. Unfold `Z` into its sum `∑ i, Real.exp (-b * 𝓒.energy i)`:            R1
  2. Replace every `𝓒.energy i` under the `∑` by `E`, using `h`
     (`simp only [h]`; `rw [h]` fails under the binder):                   R2
     (plain `simp` also rewrites `-b * E` to `-(b * E)` on both sides:     R3)
  3. The sum of the constant `Real.exp (-b * E)` → `↑(Fintype.card ι) * …`: R4 → R5 → R6
  One `simp` call given the definition name and `h` performs steps 1–3.
-/
-- BEGIN SPEC
theorem Z_degenerate {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)
    (E b : ℝ) (h : ∀ i, 𝓒.energy i = E) :
    𝓒.mathematicalPartitionFunctionBetaReal b = Fintype.card ι * Real.exp (-b * E) :=
-- END SPEC
  by simp [mathematicalPartitionFunctionBetaReal, h]

/- SKELETON · Z_at_beta_zero
  1. Unfold `Z` at `b = 0`:                                                R1
  2. Each exponent `-0 * 𝓒.energy i` → `0`, each term `Real.exp 0` → `1`,
     each with `simp only [lemma]` (`0 * 𝓒.energy i` mentions the bound `i`,
     so `rw [zero_mul]` fails under the `∑`, as in R2):                   R7 → R8 → R9
  3. The sum of `1`s → `↑(Fintype.card ι) * 1` → `↑(Fintype.card ι)`:     R4 → R5 → R6 → R10
  As in Part 1, one `simp` call given the definition name performs steps 1–3.
-/
-- BEGIN SPEC
theorem Z_at_beta_zero {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) :
    𝓒.mathematicalPartitionFunctionBetaReal 0 = Fintype.card ι :=
-- END SPEC
  by simp [mathematicalPartitionFunctionBetaReal]

end E117

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the partition function first (R1): `simp` treats the name as opaque until you name it. After
    that, every term of the sum is the same constant (once the energies are `E`, or once `b = 0`).
H2. Make each term constant (R2 with `h`; R7–R9 at `b = 0`), then evaluate the sum of a constant with
    R4 → R5 → R6 (and R10). `simp` knows R3–R10 by itself; it needs only the definition name and `h`.
H3. `simp [mathematicalPartitionFunctionBetaReal, h]` for `Z_degenerate`; the same `simp` without `h`
    for `Z_at_beta_zero`. (`rw [h]` fails: `𝓒.energy i` sits under the `∑` binder.)
-/
