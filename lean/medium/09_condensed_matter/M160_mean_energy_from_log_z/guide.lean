/- Guide for M160 (Mean energy from log Z).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`𝓔 : CanonicalEnsemble ι` is any physlib canonical ensemble with microstates `ι`.
`HasDerivAt f f' x` (Mathlib): the function `f : ℝ → ℝ` is differentiable at `x` with derivative `f'`.
Part W: worked combinations on objects that are NOT the exercise's (plain weights, other exponents).
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

open CanonicalEnsemble Real

namespace M160Guide

/-! # Part R · Reference entries -/

/-! ## Facts about the partition function -/

/-! ### R1. `have hZ := 𝓔.mathematicalPartitionFunctionBetaReal_pos b` · context gains `0 < Z(b)`
Needs `[Nonempty ι]`: at least one microstate, so the sum of positive terms is positive. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (G : Prop) (g : 0 < 𝓔.mathematicalPartitionFunctionBetaReal b → G) : G := by
  have hZ := 𝓔.mathematicalPartitionFunctionBetaReal_pos b
  exact g hZ

/-! ### R2. `unfold mathematicalPartitionFunctionBetaReal` · goal: the FUNCTION `Z` → `fun b => ∑ …`
Here `Z` appears without an argument (`HasDerivAt Z …` is about the function). `unfold` turns the bare
name into a `fun`; `simp only [mathematicalPartitionFunctionBetaReal]` only rewrites `Z b` applied. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι)
    (P : (ℝ → ℝ) → Prop) (h : P (fun b => ∑ i, Real.exp (-b * 𝓔.energy i))) :
    P 𝓔.mathematicalPartitionFunctionBetaReal := by
  unfold mathematicalPartitionFunctionBetaReal
  exact h

/-! ## Differentiating a finite sum term by term -/

/-! ### R3. `Finset.sum_neg_distrib` right to left · `-∑ i, f i` → `∑ i, -f i` · goal
The lemma is `Finset.sum_neg_distrib f : ∑ x ∈ s, -f x = -∑ x ∈ s, f x`. -/
example {ι : Type} [Fintype ι] (f : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i, -f i)) :
    P (-∑ i, f i) := by
  rw [← Finset.sum_neg_distrib]
  exact h

/-! ### R4. `apply HasDerivAt.fun_sum` · goal: derivative of a sum → derivative of every term
`HasDerivAt.fun_sum : (∀ i ∈ u, HasDerivAt (A i) (A' i) x) →
  HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x`. Both the function and the claimed
derivative must already be sums over the same index set (hence R3 first). -/
example {ι : Type} [Fintype ι] (A : ι → ℝ → ℝ) (A' : ι → ℝ) (x : ℝ)
    (h : ∀ i ∈ Finset.univ, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i, A i y) (∑ i, A' i) x := by
  apply HasDerivAt.fun_sum
  exact h

/-! ### R5. `intro i _` on `∀ i ∈ s, Q i` · context gains `i` and an unnamed `i ∈ s`
`∀ i ∈ s, Q i` is `∀ i, i ∈ s → Q i`: two binders, so `intro` takes two names; `_` drops the
membership proof (it prints as `a✝`). -/
example {ι : Type} [Fintype ι] (Q : ι → Prop) (h : ∀ i, Q i) : ∀ i ∈ Finset.univ, Q i := by
  intro i _
  exact h i

/-! ### R6. `hasDerivAt_id' x` · `HasDerivAt (fun x => x) 1 x` · context gains it -/
example (x : ℝ) (G : Prop) (g : HasDerivAt (fun y => y) 1 x → G) : G := by
  have h1 := hasDerivAt_id' x
  exact g h1

/-! ### R7. `hf.neg` (`HasDerivAt.neg`) · from `hf : HasDerivAt f f' x`: `HasDerivAt (-f) (-f') x`
`-f` is the function `y ↦ -f y`; Lean keeps it as `-f`, so with `f = fun x => x` you will see
`(-fun x => x) y` (R11 turns it into `-y`). -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (-f) (-f') x → G) : G := by
  have h2 := hf.neg
  exact g h2

/-! ### R8. `hf.mul_const c` (`HasDerivAt.mul_const`) · `HasDerivAt (fun y => f y * c) (f' * c) x` -/
example (f : ℝ → ℝ) (f' x c : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (fun y => f y * c) (f' * c) x → G) : G := by
  have h2 := hf.mul_const c
  exact g h2

/-! ### R9. `hf.exp` (`HasDerivAt.exp`) · chain rule: `HasDerivAt (fun y => rexp (f y)) (rexp (f x) * f') x`
`rexp` is how Lean prints `Real.exp`. -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (G : Prop)
    (g : HasDerivAt (fun y => Real.exp (f y)) (Real.exp (f x) * f') x → G) : G := by
  have h2 := hf.exp
  exact g h2

/-! ### R10. `refine hf.congr_deriv ?_` (`HasDerivAt.congr_deriv`) · goal: `HasDerivAt f g' x` → `f' = g'`
`HasDerivAt.congr_deriv : HasDerivAt f f' x → f' = g' → HasDerivAt f g' x`: the derivative you built
(`f'`) need only be equal to the one the goal asks for (`g'`). The function `f` must match the goal's
up to unfolding (`fun y => rexp ((-fun x => x) y * c)` matches `fun y => rexp (-y * c)`). -/
example (f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (h : f' = g') : HasDerivAt f g' x := by
  refine hf.congr_deriv ?_
  exact h

/-! ### R11. `simp` on a negated function applied to a point · goal: `(-fun x => x) y` → `-y`
`simp` uses `Pi.neg_apply : (-f) y = -f y`, beta-reduces, and also normalises `-1 * c` and the signs. -/
example (y c : ℝ) (P : ℝ → Prop) (h : P (-(y * c))) : P ((-fun x => x) y * c) := by
  simp
  exact h

/-! ## The chain rule for `log` -/

/-! ### R12. `hf.log hne` (`HasDerivAt.log`) · `HasDerivAt (fun y => Real.log (f y)) (f' / f x) x`
The second argument `hne : f x ≠ 0` is needed because `log` is only differentiable away from `0`. -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (hne : f x ≠ 0) (G : Prop)
    (g : HasDerivAt (fun y => Real.log (f y)) (f' / f x) x → G) : G := by
  have h2 := hf.log hne
  exact g h2

/-! ### R13. `hpos.ne'` (`LT.lt.ne'`) · from `hpos : 0 < a`: `a ≠ 0` -/
example (a : ℝ) (hpos : 0 < a) (G : Prop) (g : a ≠ 0 → G) : G := by
  have hne := hpos.ne'
  exact g hne

/-! ## Mean energy as a ratio -/

/-! ### R14. `simp only [meanEnergyBetaReal]` · goal: `U(b)` → `∑ i, E i * p b i` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, 𝓔.energy i * 𝓔.probabilityBetaReal b i)) :
    P (𝓔.meanEnergyBetaReal b) := by
  simp only [meanEnergyBetaReal]
  exact h

/-! ### R15. `simp only [probabilityBetaReal]` · goal: every `p b i` → `exp (-b E i) / Z(b)`, also under `∑` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)
    (w : ι → ℝ) (P : ℝ → Prop)
    (h : P (∑ i, w i * (Real.exp (-b * 𝓔.energy i) / 𝓔.mathematicalPartitionFunctionBetaReal b))) :
    P (∑ i, w i * 𝓔.probabilityBetaReal b i) := by
  simp only [probabilityBetaReal]
  exact h

/-! ### R16. `mul_div_assoc` right to left · `a * (b / c)` → `a * b / c` · goal
The lemma is `mul_div_assoc a b c : a * b / c = a * (b / c)`; `a * b / c` means `(a * b) / c`. -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * b / c)) : P (a * (b / c)) := by
  simp only [← mul_div_assoc]
  exact h

/-! ### R17. `Finset.sum_div` right to left · `∑ i, f i / a` → `(∑ i, f i) / a` · goal
The lemma is `Finset.sum_div s f a : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`. -/
example {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P ((∑ i, f i) / a)) :
    P (∑ i, f i / a) := by
  simp only [← Finset.sum_div]
  exact h

/-! ### R18. `ring` · closes a field identity with division: `/ c` is `* c⁻¹`, `c` an unknown
No `c ≠ 0` is needed for an identity that holds for `c⁻¹` as an unknown. A sum `∑ …` is an unknown too. -/
example (s c : ℝ) : -s / c = -(s / c) := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One exponential with exponent `-y * 3`: R6 → R7 → R8 → R9, matched by R10, side goal R11 + ring -/
example (x : ℝ) : HasDerivAt (fun y => Real.exp (-y * 3)) (-(3 * Real.exp (-x * 3))) x := by
  refine (((hasDerivAt_id' x).neg.mul_const 3).exp).congr_deriv ?_
  simp
  ring

/-! ### W2. A sum of exponentials with positive exponents `y * a i`: R4, R5, then R6 → R8 → R9, R10 -/
example {ι : Type} [Fintype ι] (a : ι → ℝ) (x : ℝ) :
    HasDerivAt (fun y => ∑ i, Real.exp (y * a i)) (∑ i, a i * Real.exp (x * a i)) x := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (((hasDerivAt_id' x).mul_const (a i)).exp).congr_deriv (by ring)

/-! ### W3. `log` of a positive function: R12 with R13, then R10 -/
example (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) (hpos : 0 < f x) :
    HasDerivAt (fun y => Real.log (f y)) (f' * (f x)⁻¹) x := by
  refine (hf.log hpos.ne').congr_deriv ?_
  ring

/-! ### W4. Pulling a common denominator out of a weighted sum: R16, R17, R18 -/
example {ι : Type} [Fintype ι] (a w : ι → ℝ) (s : ℝ) :
    (∑ i, a i * w i) / s = ∑ i, a i * (w i / s) := by
  simp only [← mul_div_assoc]
  simp only [← Finset.sum_div]

end M160Guide
