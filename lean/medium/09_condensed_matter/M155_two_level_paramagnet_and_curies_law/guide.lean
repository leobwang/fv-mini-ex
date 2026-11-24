/- Guide for M155 (Two-level paramagnet and Curie's law).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`𝓒 : CanonicalEnsemble ι` is any physlib canonical ensemble with microstates `ι`; `T : Temperature`.
Part W: worked combinations on objects that are NOT the exercise's (other energies, other functions).
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open CanonicalEnsemble Real

namespace M155Guide

/-! # Part R · Reference entries -/

/-! ## Boltzmann probabilities of a finite ensemble -/

/-! ### R1. `simp only [probability]` · goal: `𝓒.probability T i` → `rexp (-↑T.β * E i) / Z`
`𝓒.probability T i` is defined as `rexp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T`.
`simp only` unfolds every occurrence (`rw` would unfold only the first one's pattern). -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (i : ι)
    (P : ℝ → Prop) (h : P (rexp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T)) :
    P (𝓒.probability T i) := by
  simp only [probability]
  exact h

/-! ### R2. `mathematicalPartitionFunction_of_fintype` · goal: `Z` → `∑ i, rexp (-↑T.β * E i)`
Needs `[IsFinite 𝓒]` (counting measure, no continuous degrees of freedom) and
`[MeasurableSingletonClass ι]` (every single microstate is a measurable set); `twoState a b` over
`Fin 2` has both. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓒 : CanonicalEnsemble ι) [IsFinite 𝓒]
    (T : Temperature) (P : ℝ → Prop) (h : P (∑ i, rexp (-↑T.β * 𝓒.energy i))) :
    P (𝓒.mathematicalPartitionFunction T) := by
  rw [mathematicalPartitionFunction_of_fintype]
  exact h

/-! ### R3. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {M : Type} [AddCommMonoid M] (f : Fin 2 → M) (P : M → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R4. `twoState_energy_fst`, `twoState_energy_snd` · goal: the two energies of `twoState a b`
`twoState a b : CanonicalEnsemble (Fin 2)` has state `0` at energy `a`, state `1` at energy `b`. -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P a b) :
    P ((twoState a b).energy 0) ((twoState a b).energy 1) := by
  simp only [twoState_energy_fst, twoState_energy_snd]
  exact h

/-! ### R5. `neg_mul`, `mul_neg`, `neg_neg` · goal: signs pulled out of products, `- -x` → `x`
`neg_mul a b : -a * b = -(a * b)`, `mul_neg a b : a * -b = -(a * b)`, `neg_neg x : - -x = x`.
Plain `simp` uses all three by itself. -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P (a * b) (-(a * b))) : P (-a * -b) (-a * b) := by
  simp only [neg_mul, mul_neg, neg_neg]
  exact h

/-! ### R6. `Real.tanh_eq` · `tanh x = (rexp x - rexp (-x)) / (rexp x + rexp (-x))` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((rexp x - rexp (-x)) / (rexp x + rexp (-x)))) :
    P (Real.tanh x) := by
  rw [Real.tanh_eq]
  exact h

/-! ### R7. `sub_div` · `(a - b) / c = a / c - b / c` · goal: split a difference over a common divisor -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a / c - b / c)) : P ((a - b) / c) := by
  rw [sub_div]
  exact h

/-! ## Derivatives: `HasDerivAt f f' x` -/

/-! ### R8. `Real.tanh_eq_sinh_div_cosh` · `tanh x = sinh x / cosh x` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.sinh x / Real.cosh x)) : P (Real.tanh x) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact h

/-! ### R9. `hasDerivAt_id x` · context gains `HasDerivAt id 1 x` (the identity has derivative 1) -/
example (x : ℝ) (G : Prop) (g : HasDerivAt id 1 x → G) : G := by
  have h1 := hasDerivAt_id x
  exact g h1

/-! ### R10. `hf.const_mul c` (`HasDerivAt.const_mul`) · context gains the derivative of `c * f y`
`hf : HasDerivAt f f' x` gives `hf.const_mul c : HasDerivAt (fun y => c * f y) (c * f') x`. -/
example (f : ℝ → ℝ) (f' x c : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (fun y => c * f y) (c * f') x → G) : G := by
  have hc := hf.const_mul c
  exact g hc

/-! ### R11. `simpa using e` · closes the goal when `simp` brings `e`'s type and the goal to the same form
Here `simp` turns `id y` into `y` and `c * 1` into `c`, on both sides. -/
example (c x : ℝ) (e : HasDerivAt (fun y => c * id y) (c * 1) x) :
    HasDerivAt (fun y => c * y) c x := by
  simpa using e

/-! ### R12. `Real.hasDerivAt_sinh x` · context gains `HasDerivAt sinh (cosh x) x` -/
example (x : ℝ) (G : Prop) (g : HasDerivAt Real.sinh (Real.cosh x) x → G) : G := by
  have hs := Real.hasDerivAt_sinh x
  exact g hs

/-! ### R13. `Real.hasDerivAt_cosh x` · context gains `HasDerivAt cosh (sinh x) x` -/
example (x : ℝ) (G : Prop) (g : HasDerivAt Real.cosh (Real.sinh x) x → G) : G := by
  have hc := Real.hasDerivAt_cosh x
  exact g hc

/-! ### R14. `hf.comp x hg` (`HasDerivAt.comp`, the chain rule) · context gains the derivative of `f ∘ g`
`hf : HasDerivAt f f' (g x)` (derivative of the outer function AT `g x`) and `hg : HasDerivAt g g' x`
give `HasDerivAt (f ∘ g) (f' * g') x`. -/
example (f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' (g x)) (hg : HasDerivAt g g' x)
    (G : Prop) (k : HasDerivAt (f ∘ g) (f' * g') x → G) : G := by
  have hfg := hf.comp x hg
  exact k hfg

/-! ### R15. `hc.div hd hx` (`HasDerivAt.div`, the quotient rule) · context gains the derivative of `c / d`
`hx : d x ≠ 0`. The value is `(c' * d x - c x * d') / d x ^ 2`; `c / d` is the function `y ↦ c y / d y`. -/
example (c d : ℝ → ℝ) (c' d' x : ℝ) (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
    (hx : d x ≠ 0) (G : Prop)
    (k : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x → G) : G := by
  have hq := hc.div hd hx
  exact k hq

/-! ### R16. `(Real.cosh_pos x).ne'` · closes `cosh x ≠ 0`
`Real.cosh_pos x : 0 < cosh x`; for `h : a < b`, `h.ne' : b ≠ a` (lemma `LT.lt.ne'`). -/
example (x : ℝ) : Real.cosh x ≠ 0 := by
  exact (Real.cosh_pos x).ne'

/-! ### R17. `refine hf.congr_deriv ?_` (`HasDerivAt.congr_deriv`) · goal: same function, other value
`hf : HasDerivAt f f' x` proves `HasDerivAt f g' x` once you show `f' = g'`. -/
example (f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (e : f' = g') :
    HasDerivAt f g' x := by
  refine hf.congr_deriv ?_
  exact e

/-! ### R18. `Function.comp_apply` · `(f ∘ g) x = f (g x)` · goal -/
example (f g : ℝ → ℝ) (x : ℝ) (P : ℝ → Prop) (h : P (f (g x))) : P ((f ∘ g) x) := by
  rw [Function.comp_apply]
  exact h

/-! ### R19. `mul_zero`, `Real.sinh_zero`, `Real.cosh_zero` · goal: `sinh (c * 0)` → `0`, `cosh (c * 0)` → `1` -/
example (c : ℝ) (P : ℝ → ℝ → Prop) (h : P 0 1) : P (Real.sinh (c * 0)) (Real.cosh (c * 0)) := by
  simp only [mul_zero, Real.sinh_zero, Real.cosh_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The probability of the upper state of `twoState a b`: R1, R2, R3, R4 in one `simp only` -/
example (a b : ℝ) (T : Temperature) :
    (twoState a b).probability T 1 = rexp (-↑T.β * b) / (rexp (-↑T.β * a) + rexp (-↑T.β * b)) := by
  simp only [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two,
    twoState_energy_fst, twoState_energy_snd]

/-! ### W2. Chain rule: `y ↦ sinh (c * y)` has derivative `c` at `0`: R9 → R10 → R11, R12, R14, R17 -/
example (c : ℝ) : HasDerivAt (fun y => Real.sinh (c * y)) c 0 := by
  have hl : HasDerivAt (fun y : ℝ => c * y) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hs := (Real.hasDerivAt_sinh (c * 0)).comp 0 hl
  refine hs.congr_deriv ?_
  simp

/-! ### W3. Quotient rule: `y ↦ y / cosh y` has derivative `1` at `0`: R9, R13, R15, R16, R17 -/
example : HasDerivAt (fun y => y / Real.cosh y) 1 0 := by
  have hq := (hasDerivAt_id (0 : ℝ)).div (Real.hasDerivAt_cosh 0) (Real.cosh_pos 0).ne'
  refine hq.congr_deriv ?_
  simp

end M155Guide
