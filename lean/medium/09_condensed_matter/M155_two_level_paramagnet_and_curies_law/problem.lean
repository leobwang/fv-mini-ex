/- M155 | Two-level paramagnet and Curie's law | 15-20 min | probability, tanh, HasDerivAt, chain rule, quotient rule, physlib
GOAL
  One spin in a field `h` is physlib's `twoState (-h) h`: state `0` (up) has energy `-h`, state `1`
  (down) has energy `+h`; `p₀, p₁` are their Boltzmann probabilities and `β = (T.β : ℝ)`. Show the
  mean magnetisation `mag T h = p₀ - p₁` is `tanh (β h)`, and Curie's law: the zero-field
  susceptibility, the derivative of `h ↦ mag T h` at `h = 0`, is `β = 1 / (kB T)`.

REFERENCE
  #check CanonicalEnsemble.probability  -- 𝓒.probability T i = exp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T
  #check CanonicalEnsemble.mathematicalPartitionFunction_of_fintype  -- for twoState: Z = ∑ i, exp (-↑T.β * energy i)
  #check Fin.sum_univ_two   -- ∑ i : Fin 2, f i = f 0 + f 1
  #check Real.tanh_eq       -- tanh x = (exp x - exp (-x)) / (exp x + exp (-x))
  #check Real.tanh_eq_sinh_div_cosh  -- tanh x = sinh x / cosh x
  #check Real.hasDerivAt_sinh  -- HasDerivAt sinh (cosh x) x    (also `Real.hasDerivAt_cosh`: derivative sinh)
  #check HasDerivAt.comp    -- (hf : HasDerivAt f f' (g x)).comp x (hg : HasDerivAt g g' x) : HasDerivAt (f ∘ g) (f' * g') x
  #check HasDerivAt.div     -- hc.div hd (d x ≠ 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x
  #check HasDerivAt.congr_deriv  -- HasDerivAt f f' x → f' = g' → HasDerivAt f g' x
  example (c x : ℝ) : HasDerivAt (fun y => c * y) c x := by simpa using (hasDerivAt_id x).const_mul c
BANNED: twoState_probability_fst, twoState_probability_snd, deriv_tanh, contDiff_tanh, contDiff_top_tanh, iteratedDeriv_tanh_differentiable
NOTE: `T.β : ℝ≥0` and `(T.β : ℝ)` is its cast; `Temperature.β_toReal : (T.β : ℝ) = 1 / (kB * T.toReal)`. Mathlib has no `hasDerivAt_tanh`: go through `sinh / cosh`.
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

-- BEGIN SPEC
theorem mag_eq (T : Temperature) (h : ℝ) : mag T h = Real.tanh ((T.β : ℝ) * h) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem curie (T : Temperature) : HasDerivAt (mag T) (T.β : ℝ) 0 :=
-- END SPEC
  sorry

end M155

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `mag_eq` is pure unfolding: definitions of `mag` and `probability`, `Z` as a two-term sum, and
    the exponential form of `tanh`. Then `curie` never needs `probability` again.
H2. `curie`: rewrite `mag T` as `fun h => sinh (β h) / cosh (β h)` (by `funext` and `mag_eq`).
    Chain rule for `sinh (β h)` and `cosh (β h)` at `h = 0`, then the quotient rule; the value it
    produces mentions `sinh 0` and `cosh 0`, so fix it up with `congr_deriv`.
H3. `simp [mag, probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two, Real.tanh_eq, sub_div]`;
    `have hs := (Real.hasDerivAt_sinh (β * 0)).comp 0 hl` with `hl : HasDerivAt (fun h => β * h) β 0`;
    after `rw [hm]`, close with `(hs.div hc (Real.cosh_pos _).ne').congr_deriv (by simp)`.
-/
