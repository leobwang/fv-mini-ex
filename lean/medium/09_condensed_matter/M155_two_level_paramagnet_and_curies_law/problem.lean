/- M155 | Two-level paramagnet and Curie's law | 15-20 min | probability, tanh, HasDerivAt, chain rule, quotient rule, physlib
GOAL
  One spin in a field `h` is physlib's `twoState (-h) h`: state `0` (up) has energy `-h`, state `1`
  (down) has energy `+h`; `p₀, p₁` are their Boltzmann probabilities and `β = (T.β : ℝ)`. Show the
  mean magnetisation `mag T h = p₀ - p₁` is `tanh (β h)`, and Curie's law: the zero-field
  susceptibility, the derivative of `h ↦ mag T h` at `h = 0`, is `β = 1 / (kB T)`.

BANNED: twoState_probability_fst, twoState_probability_snd, deriv_tanh, contDiff_tanh, contDiff_top_tanh, iteratedDeriv_tanh_differentiable

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open CanonicalEnsemble Real

namespace M155

-- BEGIN SPEC
/-- Mean magnetisation `⟨M⟩ = p↑ − p↓` of one spin in a field `h`: state `0` (up) has energy
`−h`, state `1` (down) has energy `+h`. -/
noncomputable def mag (T : Temperature) (h : ℝ) : ℝ :=
  (twoState (-h) h).probability T 0 - (twoState (-h) h).probability T 1
-- END SPEC

/- SKELETON · mag_eq
  1. Unfold `mag` (a plain definition: `simp [mag, …]`), then both probabilities:   R1
  2. The partition function as a sum, then as two terms:                            R2 → R3
  3. The two energies `-h`, `h` of `twoState (-h) h`:                               R4
  4. Normalise the signs in `-↑T.β * -h` and `-↑T.β * h`:                           R5
  5. `tanh` in exponentials, split over the common divisor; both sides now agree:   R6 → R7
  All five steps fit in ONE `simp [mag, …]` call that names the lemmas of R1–R7
  (R4 and R5 are simp lemmas already).
-/
-- BEGIN SPEC
theorem mag_eq (T : Temperature) (h : ℝ) : mag T h = Real.tanh ((T.β : ℝ) * h) :=
-- END SPEC
  sorry

/- SKELETON · curie
  1. Facts first:
       hm : mag T = fun h => Real.sinh ((T.β : ℝ) * h) / Real.cosh ((T.β : ℝ) * h)
              proof: funext h, then rw [mag_eq], then R8
       hl : HasDerivAt (fun h : ℝ => (T.β : ℝ) * h) (T.β : ℝ) 0
              proof: R11 applied to R9 → R10
       hs : chain rule for `sinh` at `(T.β : ℝ) * 0` with `hl`:           R12 → R14
       hc : chain rule for `cosh` at `(T.β : ℝ) * 0` with `hl`:           R13 → R14
  2. Replace the function in the goal:                                    rw [hm]
  3. Quotient rule from `hs`, `hc` (denominator ≠ 0 by R16), then fix the
     value, which mentions `sinh (↑T.β * 0)` and `cosh (↑T.β * 0)`:       R15 with R16 → R17, simp (R18, R19)
-/
-- BEGIN SPEC
theorem curie (T : Temperature) : HasDerivAt (mag T) (T.β : ℝ) 0 :=
-- END SPEC
  sorry

end M155

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `mag_eq` is pure unfolding (R1–R7): `p₀ - p₁` with `Z` as a two-term sum is literally `tanh` in
    exponential form once the signs are normalised. `curie` never needs `probability` again: it
    starts from `mag_eq`, because Mathlib differentiates `sinh` and `cosh` but not `tanh`.
H2. `curie`: prove `hm : mag T = fun h => sinh (β h) / cosh (β h)` (`funext`, `mag_eq`, R8) and the
    inner derivative `hl` of `h ↦ β h`; chain rule (R14) for `sinh` and `cosh` at `β * 0`; `rw [hm]`;
    quotient rule (R15); its value mentions `sinh (β * 0)` and `cosh (β * 0)`, so finish with
    `congr_deriv` (R17) and `simp`.
H3. `simp [mag, probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two, Real.tanh_eq, sub_div]`;
    `have hs := (Real.hasDerivAt_sinh ((T.β : ℝ) * 0)).comp 0 hl` with
    `hl : HasDerivAt (fun h : ℝ => (T.β : ℝ) * h) (T.β : ℝ) 0` from
    `simpa using (hasDerivAt_id (0 : ℝ)).const_mul (T.β : ℝ)`;
    after `rw [hm]`, close with `(hs.div hc (Real.cosh_pos _).ne').congr_deriv (by simp)`.
-/
