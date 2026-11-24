/- Guide for H089 (Heat capacity as an energy variance).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a derivative fact (`hf.neg`, `hc.div hd hx`, …) use `have h := …`, so the
context gains `h` and you can read off exactly what the lemma produced.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace H089Guide

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]

/-! # Part R · Reference entries -/

/-! ## Derivatives of sums of exponentials -/

/-! ### R1. `unfold mathematicalPartitionFunctionBetaReal` · goal: the name `Z` → its defining sum
`Z` is a function `ℝ → ℝ`, so it unfolds to a `fun`. The same works on `probabilityBetaReal`,
`meanEnergyBetaReal` (R12). -/
example (𝓒 : CanonicalEnsemble ι) (P : (ℝ → ℝ) → Prop)
    (h : P (fun t => ∑ i, rexp (-t * 𝓒.energy i))) : P 𝓒.mathematicalPartitionFunctionBetaReal := by
  unfold mathematicalPartitionFunctionBetaReal
  exact h

/-! ### R2. `Finset.sum_neg_distrib` · `∑ i ∈ s, -f i = -∑ i ∈ s, f i`; `rw [← …]` pushes `-` inside -/
example (f : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, -f i)) : P (-∑ i, f i) := by
  rw [← Finset.sum_neg_distrib]
  exact h

/-! ### R3. `apply HasDerivAt.fun_sum` · goal: derivative of a sum → derivative of each term -/
example (A : ι → ℝ → ℝ) (A' : ι → ℝ) (x : ℝ) (h : ∀ i ∈ Finset.univ, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i, A i y) (∑ i, A' i) x := by
  apply HasDerivAt.fun_sum
  exact h

/-! ### R4. `hasDerivAt_id'` · context gains `(fun y => y)' = 1` -/
example (x : ℝ) : HasDerivAt (fun y => y) 1 x := by
  have h := hasDerivAt_id' x
  exact h

/-! ### R5. `HasDerivAt.neg` · `f' ↦ -f'`; the function becomes `-f` (a negated function) -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) : HasDerivAt (-f) (-f') x := by
  have h := hf.neg
  exact h

/-! ### R6. `HasDerivAt.mul_const` · `hc.mul_const d`: `(c y * d)' = c' * d` -/
example (c : ℝ → ℝ) (c' d x : ℝ) (hc : HasDerivAt c c' x) :
    HasDerivAt (fun y => c y * d) (c' * d) x := by
  have h := hc.mul_const d
  exact h

/-! ### R7. `HasDerivAt.exp` · chain rule for `Real.exp`: `(exp (f y))' = exp (f x) * f'` -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => rexp (f y)) (rexp (f x) * f') x := by
  have h := hf.exp
  exact h

/-! ### R8. `HasDerivAt.congr_deriv` · goal: `HasDerivAt f g' x` → the algebra goal `f' = g'`
Use it when you have `hf : HasDerivAt f f' x` and `f'` is `g'` only up to algebra. -/
example (f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (e : f' = g') : HasDerivAt f g' x := by
  refine hf.congr_deriv ?_
  exact e

/-! ### R9. `simp` · goal: `(-fun y => y) x` (negated identity, applied) → `-x`; `-1 * c` → `-c` -/
example (x c : ℝ) (P : ℝ → Prop) (h : P (-(x * c))) : P ((-fun y => y) x * c) := by
  simp
  exact h

/-! ### R10. `HasDerivAt.const_mul` · `hd.const_mul c`: `(c * d y)' = c * d'` -/
example (d : ℝ → ℝ) (c d' x : ℝ) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c * d y) (c * d') x := by
  have h := hd.const_mul c
  exact h

/-! ## Mean energy as a quotient -/

/-! ### R11. `funext x` · goal: equation of functions `f = g` → `f x = g x` for a fresh `x` -/
example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R12. `simp only [meanEnergyBetaReal, probabilityBetaReal]` · goal: `U t` → `∑ i, E i * (exp/Z)` -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (P : ℝ → Prop)
    (h : P (∑ i, 𝓒.energy i * (rexp (-t * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal t))) :
    P (𝓒.meanEnergyBetaReal t) := by
  simp only [meanEnergyBetaReal, probabilityBetaReal]
  exact h

/-! ### R13. `Finset.sum_div` · `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a` -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (∑ i, f i / a)) : P ((∑ i, f i) / a) := by
  rw [Finset.sum_div]
  exact h

/-! ### R14. `mul_div_assoc` · `a * b / c = a * (b / c)` -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * (b / c))) : P (a * b / c) := by
  rw [mul_div_assoc]
  exact h

/-! ## The variance identity -/

/-! ### R15. `mathematicalPartitionFunctionBetaReal_pos` · context gains `0 < Z t` (needs `[Nonempty ι]`) -/
example [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)
    (g : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t → G) : G := by
  have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos t
  exact g hZ

/-! ### R16. `simp only [e]` with `e : ∀ …, l = r` · goal: rewrites `l` inside `∑ i, …`, where `rw` cannot -/
example (w : ι → ℝ) (c : ℝ) (e : ∀ a b : ℝ, a * (b + 1) = a * b + a) (P : ℝ → Prop)
    (h : P (∑ i, (w i * c + w i))) : P (∑ i, w i * (c + 1)) := by
  simp only [e]
  exact h

/-! ### R17. `Finset.sum_add_distrib` · `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i` -/
example (f g : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, f i + ∑ i, g i)) : P (∑ i, (f i + g i)) := by
  rw [Finset.sum_add_distrib]
  exact h

/-! ### R18. `Finset.sum_sub_distrib` · `∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i` -/
example (f g : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, f i - ∑ i, g i)) : P (∑ i, (f i - g i)) := by
  rw [Finset.sum_sub_distrib]
  exact h

/-! ### R19. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `rw [← …]` pulls `a` out -/
example (f : ι → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (a * ∑ i, f i)) : P (∑ i, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R20. `have hd : body = name := rfl` · context gains the definition as an equation
A definition holds by `rfl`. `simp only [hd]` then folds the sum back into the name `Z t`. -/
example (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)
    (g : ∑ i, rexp (-t * 𝓒.energy i) = 𝓒.mathematicalPartitionFunctionBetaReal t → G) : G := by
  have hd : ∑ i, rexp (-t * 𝓒.energy i) = 𝓒.mathematicalPartitionFunctionBetaReal t := rfl
  exact g hd

/-! ### R21. `generalize e = z at *` · goal and context: every copy of the term `e` → a fresh `z`
Without `at *` only the goal changes. -/
example (f : ℝ → ℝ) (t : ℝ) (hpos : 0 < f t) (P : ℝ → Prop) (h : ∀ z : ℝ, 0 < z → P z) :
    P (f t) := by
  generalize f t = z at *
  exact h z hpos

/-! ### R22. `field_simp` · goal: multiplies out denominators it can prove nonzero (from `hz : 0 < z`) -/
example (a b z : ℝ) (hz : 0 < z) (h : a = z * b) : a / z = b := by
  field_simp
  exact h

/-! ## The quotient rule -/

/-! ### R23. `HasDerivAt.div` · `hc.div hd hx`: `(c / d)' = (c' * d x - c x * d') / d x ^ 2` -/
example (c d : ℝ → ℝ) (c' d' x : ℝ) (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
    (hx : d x ≠ 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x := by
  have h := hc.div hd hx
  exact h

/-! ### R24. `LT.lt.ne'` · `hz.ne'` turns `hz : 0 < z` into `z ≠ 0` -/
example (z : ℝ) (hz : 0 < z) : z ≠ 0 := by
  have h := hz.ne'
  exact h

/-! ### R25. `beta_reduce` · goal: `(fun x => body) t` → `body` with `t` for `x` -/
example (f : ℝ → ℝ) (t : ℝ) (P : ℝ → Prop) (h : P (f t + 1)) : P ((fun x => f x + 1) t) := by
  beta_reduce
  exact h

/-! ## Monotonicity from the sign of the derivative -/

/-! ### R26. `apply antitone_of_deriv_nonpos` · goal list: `Antitone f` → differentiable, `deriv ≤ 0` -/
example (f : ℝ → ℝ) (h1 : Differentiable ℝ f) (h2 : ∀ x, deriv f x ≤ 0) : Antitone f := by
  apply antitone_of_deriv_nonpos
  exact h1
  exact h2

/-! ### R27. `intro x` on `Differentiable ℝ f` · goal: `DifferentiableAt ℝ f x` for a fresh `x`
`Differentiable ℝ f` is by definition `∀ x, DifferentiableAt ℝ f x`. -/
example (f : ℝ → ℝ) (h : ∀ x, DifferentiableAt ℝ f x) : Differentiable ℝ f := by
  intro x
  exact h x

/-! ### R28. `HasDerivAt.differentiableAt` · `hf.differentiableAt : DifferentiableAt ℝ f x` -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) : DifferentiableAt ℝ f x := by
  have h := hf.differentiableAt
  exact h

/-! ### R29. `HasDerivAt.deriv` · `rw [hf.deriv]` · goal: `deriv f x` → `f'` -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (P : ℝ → Prop) (h : P f') :
    P (deriv f x) := by
  rw [hf.deriv]
  exact h

/-! ### R30. `neg_nonpos` · `-a ≤ 0 ↔ 0 ≤ a` · goal -/
example (a : ℝ) (h : 0 ≤ a) : -a ≤ 0 := by
  rw [neg_nonpos]
  exact h

/-! ### R31. `Finset.sum_nonneg` · goal: `0 ≤ ∑ i ∈ s, f i` → `∀ i ∈ s, 0 ≤ f i` -/
example (f : ι → ℝ) (h : ∀ i ∈ Finset.univ, 0 ≤ f i) : 0 ≤ ∑ i, f i := by
  apply Finset.sum_nonneg
  exact h

/-! ### R32. `mul_nonneg` · goal list: `0 ≤ a * b` → `0 ≤ a`, `0 ≤ b` -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  apply mul_nonneg
  exact ha
  exact hb

/-! ### R33. `sq_nonneg` · closes `0 ≤ a ^ 2` -/
example (a : ℝ) : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

/-! ### R34. `div_pos` · goal list: `0 < a / b` → `0 < a`, `0 < b` -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  apply div_pos
  exact ha
  exact hb

/-! ### R35. `Real.exp_pos` · closes `0 < rexp x` -/
example (x : ℝ) : 0 < rexp x := by
  exact Real.exp_pos x

/-! ### R36. `LT.lt.le` · `h.le` turns `h : a < b` into `a ≤ b` -/
example (a b : ℝ) (hab : a < b) : a ≤ b := by
  have h := hab.le
  exact h

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. A derivative chain R4 → R6 → R7, fixed up with R8 + `simp; ring` -/
example (a x : ℝ) : HasDerivAt (fun y => rexp (y * a)) (a * rexp (x * a)) x := by
  refine ((hasDerivAt_id' x).mul_const a).exp.congr_deriv ?_
  simp
  ring

/-! ### W2. A sum of such terms: R2-style sign handling is not needed here, only R3, `intro`, W1 -/
example (a : ι → ℝ) (x : ℝ) :
    HasDerivAt (fun y => ∑ i, rexp (y * a i)) (∑ i, a i * rexp (x * a i)) x := by
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hasDerivAt_id' x).mul_const (a i)).exp.congr_deriv (by simp; ring)

/-! ### W3. Quotient rule on `y ↦ y / exp y` (R4, R7, R23, R24, R8), then R21 → R22 on the algebra -/
example (x : ℝ) :
    HasDerivAt (fun y => y / rexp y) ((1 - x) / rexp x) x := by
  have hE := Real.exp_pos x
  refine ((hasDerivAt_id' x).div (hasDerivAt_id' x).exp hE.ne').congr_deriv ?_
  generalize rexp x = E at *
  field_simp

/-! ### W4. Sign of a derivative → antitone: one `HasDerivAt` fact `hd` feeds R26 → R27, R28, R29 -/
example : Antitone (fun y : ℝ => -y) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -y) (-1) x := fun x => (hasDerivAt_id' x).neg
  apply antitone_of_deriv_nonpos
  · intro x
    exact (hd x).differentiableAt
  · intro x
    rw [(hd x).deriv]
    norm_num

end H089Guide
