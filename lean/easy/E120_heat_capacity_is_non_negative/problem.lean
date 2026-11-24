/- E120 | Heat capacity is non-negative | 3 min | heatCapacity, fluctuation-dissipation, instance arguments, integral_nonneg, physlib
GOAL
  physlib defines the heat capacity `C(T) = dU/dT` (`U` = mean energy). Use its fluctuation-dissipation
  theorem `C = Var(E) / (k_B T²)` to show `C ≥ 0` for every finite canonical ensemble at `T > 0`.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Constants

namespace E120

/- SKELETON · heatCapacity_nonneg
  1. Replace the derivative `C` by the fluctuation-dissipation quotient:      R1
       goal becomes  0 ≤ 𝓒.energyVariance T / (kB * ↑T.val ^ 2)
  2. Put `0 < kB` in the context, for step 5:                                  R2
  3. Split the quotient: numerator (case ha), denominator (case hb):           R3
  4. Numerator: the variance is an integral of a square (R4 shows it):
       integral → integrand ≥ 0 pointwise → a square                           R4, R5 → R6 → R7
  5. Denominator `kB * ↑T.val ^ 2`, using `hk` from step 2:                    R8
  Steps 3–5 also fit in one `exact` term (W2).
-/
-- BEGIN SPEC
theorem heatCapacity_nonneg {ι : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature)
    (hT : 0 < T.val) : 0 ≤ 𝓒.heatCapacity T :=
-- END SPEC
  sorry

end E120

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do not differentiate anything: physlib already proved `C = Var(E) / (k_B T²)` (R1). After that
    rewrite the problem is pure sign-checking of a quotient.
H2. `0 ≤ a / b` from `0 ≤ a` and `0 ≤ b` (R3). Numerator: `energyVariance` is an integral of a square,
    so `integral_nonneg` and `sq_nonneg` (R4–R7). Denominator: `positivity`, but only after `0 < kB` is a
    hypothesis (R2, R8).
H3. `rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]`, `have hk := kB_pos`, then
    `exact div_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _) (by positivity)`.
-/
