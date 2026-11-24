/- Guide for M161 (Entropy of a two-level system).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`𝓒 : CanonicalEnsemble ι` is any physlib canonical ensemble with microstates `ι`; `T : Temperature`
is any temperature, `↑T.β : ℝ` its inverse temperature `1 / (kB T)`.
Part W: worked combinations on objects that are NOT the exercise's (a generic 2-state ensemble,
other exponents).
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Constants Real

namespace M161Guide

/-! # Part R · Reference entries -/

/-! ## From thermodynamic to Shannon entropy -/

/-! ### R1. `rw [thermodynamicEntropy_eq_shannonEntropy]` · goal: `S(T)` → `S_Shannon(T)`
For a finite ensemble (`[𝓒.IsFinite]`: counting measure, no continuous degrees of freedom) the
thermodynamic entropy equals the Shannon entropy of the Boltzmann distribution. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature) (P : ℝ → Prop)
    (h : P (𝓒.shannonEntropy T)) : P (𝓒.thermodynamicEntropy T) := by
  rw [thermodynamicEntropy_eq_shannonEntropy]
  exact h

/-! ### R2. `rw [shannonEntropy]` · goal: `S_Shannon(T)` → `-kB * ∑ i, p i * log (p i)` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (P : ℝ → Prop) (h : P (-kB * ∑ i, 𝓒.probability T i * Real.log (𝓒.probability T i))) :
    P (𝓒.shannonEntropy T) := by
  rw [shannonEntropy]
  exact h

/-! ## Boltzmann probabilities of a finite ensemble (`simp` applies R3–R8 when named or tagged) -/

/-! ### R3. `rw [probability]` · goal: `p i` → `rexp (-↑T.β * E i) / Z(T)` -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (i : ι)
    (P : ℝ → Prop)
    (h : P (Real.exp (-(T.β : ℝ) * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T)) :
    P (𝓒.probability T i) := by
  rw [probability]
  exact h

/-! ### R4. `rw [mathematicalPartitionFunction_of_fintype]` · goal: `Z(T)` → `∑ i, rexp (-↑T.β * E i)` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature) (P : ℝ → Prop)
    (h : P (∑ i, Real.exp (-(T.β : ℝ) * 𝓒.energy i))) :
    P (𝓒.mathematicalPartitionFunction T) := by
  rw [mathematicalPartitionFunction_of_fintype]
  exact h

/-! ### R5. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R6. `twoState_energy_fst`, `twoState_energy_snd` · goal: energies of `twoState E₀ E₁`
Both are `@[simp]` lemmas, so `simp` applies them without being told. -/
example (E₀ E₁ : ℝ) (P : ℝ → ℝ → Prop) (h : P E₀ E₁) :
    P ((twoState E₀ E₁).energy 0) ((twoState E₀ E₁).energy 1) := by
  simp only [twoState_energy_fst, twoState_energy_snd]
  exact h

/-! ### R7. `neg_mul` · `-a * b = -(a * b)` · goal; `simp` always rewrites in this direction -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (-(a * b))) : P (-a * b) := by
  rw [neg_mul]
  exact h

/-! ### R8. `mul_zero`, `Real.exp_zero` · goal: `rexp (-a * 0)` → `1` -/
example (a : ℝ) (P : ℝ → Prop) (h : P 1) : P (Real.exp (-a * 0)) := by
  simp only [mul_zero, Real.exp_zero]
  exact h

/-! ## One variable for `βε` -/

/-! ### R9. `rw [show u = v by ring]` · goal: put one subterm into the shape another part has -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P (-(a * b)) (-(a * b))) : P (-a * b) (-(a * b)) := by
  rw [show -a * b = -(a * b) by ring]
  exact h

/-! ### R10. `generalize e = x` · goal: every literal `e` → a fresh `x`; context gains `x : ℝ`
Only occurrences that are literally `e` are replaced, so first make them all look the same (R9). -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : ∀ x, P x (-x)) : P (a * b) (-(a * b)) := by
  generalize a * b = x
  exact h x

/-! ## Logarithms of quotients -/

/-! ### R11. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` built from positive pieces -/
example (x : ℝ) : 0 < 1 + Real.exp (-x) := by
  positivity

/-! ### R12. `hD.ne'` · `hD : 0 < D` gives `D ≠ 0` (lemma `LT.lt.ne'`: `a < b → b ≠ a`) -/
example (D : ℝ) (hD : 0 < D) (G : Prop) (g : D ≠ 0 → G) : G := by
  have hD0 : D ≠ 0 := hD.ne'
  exact g hD0

/-! ### R13. `Real.log_div` · `x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y` · goal
Give the two side conditions as arguments: `rw [Real.log_div hx hy]`. -/
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (P : ℝ → Prop) (h : P (Real.log x - Real.log y)) :
    P (Real.log (x / y)) := by
  rw [Real.log_div hx hy]
  exact h

/-! ### R14. `Real.log_one` · `log 1 = 0` · goal -/
example (P : ℝ → Prop) (h : P 0) : P (Real.log 1) := by
  rw [Real.log_one]
  exact h

/-! ### R15. `Real.log_exp` · `log (rexp x) = x` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) : P (Real.log (Real.exp x)) := by
  rw [Real.log_exp]
  exact h

/-! ## Algebra with exponentials -/

/-! ### R16. `Real.exp_add` right to left · `rexp x * rexp y` → `rexp (x + y)` · goal
The lemma is `Real.exp_add x y : rexp (x + y) = rexp x * rexp y`. -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R17. `div_eq_div_iff hb hd` · goal `a / b = c / d` → `a * d = c * b` (cross-multiply) -/
example {G₀ : Type} [CommGroupWithZero G₀] (a b c d : G₀) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : a / b = c / d := by
  rw [div_eq_div_iff hb hd]
  exact h

/-! ### R18. `linear_combination k * he` · closes `L = R` when `L - R = k * (he.lhs - he.rhs)` by `ring` -/
example (u v k : ℝ) (he : u * v = 1) : k * u * v = k := by
  linear_combination k * he

/-! ### R19. `field_simp` · goal: clear every denominator it can prove nonzero (`/` → `*`) -/
example (a b c D : ℝ) (hD : 0 < D) (h : a + b = D * c) : a / D + b / D = c := by
  field_simp
  exact h

/-! ### R20. `ring` · closes a commutative-ring identity; `rexp (…)` and `log (…)` count as unknowns -/
example (k L y : ℝ) : -(k * (0 - L + y * (-1 - L))) = k * ((1 + y) * L + y) := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Probability of state 0 in any 2-state finite ensemble: R3, R4, R5 -/
example (𝓔 : CanonicalEnsemble (Fin 2)) [𝓔.IsFinite] (T : Temperature) :
    𝓔.probability T 0 = Real.exp (-(T.β : ℝ) * 𝓔.energy 0) /
      (Real.exp (-(T.β : ℝ) * 𝓔.energy 0) + Real.exp (-(T.β : ℝ) * 𝓔.energy 1)) := by
  rw [probability]
  rw [mathematicalPartitionFunction_of_fintype]
  rw [Fin.sum_univ_two]

/-! ### W2. A log of a Boltzmann ratio: R11, R13, R15 -/
example (y : ℝ) :
    Real.log (Real.exp y / (2 + Real.exp y)) = y - Real.log (2 + Real.exp y) := by
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_exp]

/-! ### W3. Moving `exp` from denominator to numerator: R16, R17, R18 -/
example (y : ℝ) : 2 / (Real.exp y + 1) = 2 * Real.exp (-y) / (1 + Real.exp (-y)) := by
  have he : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-2) * he

/-! ### W4. Clearing a positive denominator, then `ring`: R11, R19, R20 -/
example (k y : ℝ) :
    k * (Real.exp y / (2 + Real.exp y) * y) + k * (2 / (2 + Real.exp y) * y) = k * y := by
  have hD : 0 < 2 + Real.exp y := by positivity
  field_simp
  ring

end M161Guide
