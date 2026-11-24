/- Guide for M156 (Two-level system freezes out).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`𝓒 : CanonicalEnsemble ι` is any physlib canonical ensemble with finitely many microstates `ι`;
`x : ℝ` is an inverse temperature. `l : Filter α` is any "limit point", such as `atTop`.
Part W: worked combinations on objects that are NOT the exercise's (other functions, other states).
Assumed: Lean basics.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Real Filter Topology

namespace M156Guide

/-! # Part R · Reference entries -/

/-! ## Unfolding the β-parameterised mean energy of a finite ensemble -/

/-! ### R1. `meanEnergyBetaReal` · goal: `𝓒.meanEnergyBetaReal x` → `∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal x i`
A plain definition: `simp only [meanEnergyBetaReal]` (or `simp [meanEnergyBetaReal]`) unfolds it. -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (x : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal x i)) :
    P (𝓒.meanEnergyBetaReal x) := by
  simp only [meanEnergyBetaReal]
  exact h

/-! ### R2. `probabilityBetaReal` · goal: `𝓒.probabilityBetaReal x i` → `rexp (-x * 𝓒.energy i) / Z(x)` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (x : ℝ) (i : ι)
    (P : ℝ → Prop) (h : P (rexp (-x * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal x)) :
    P (𝓒.probabilityBetaReal x i) := by
  simp only [probabilityBetaReal]
  exact h

/-! ### R3. `mathematicalPartitionFunctionBetaReal` · goal: `Z(x)` → `∑ i, rexp (-x * 𝓒.energy i)` -/
example {ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (x : ℝ)
    (P : ℝ → Prop) (h : P (∑ i, rexp (-x * 𝓒.energy i))) :
    P (𝓒.mathematicalPartitionFunctionBetaReal x) := by
  simp only [mathematicalPartitionFunctionBetaReal]
  exact h

/-! ### R4. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {M : Type} [AddCommMonoid M] (f : Fin 2 → M) (P : M → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R5. `twoState_energy_fst`, `twoState_energy_snd` · goal: the two energies of `twoState a b`
`twoState a b : CanonicalEnsemble (Fin 2)` has state `0` at energy `a`, state `1` at energy `b`.
Both are `@[simp]` lemmas: plain `simp` applies them by itself. -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : P a b) :
    P ((twoState a b).energy 0) ((twoState a b).energy 1) := by
  simp only [twoState_energy_fst, twoState_energy_snd]
  exact h

/-! ## Cleaning up a zero energy (plain `simp` does all of these by itself) -/

/-! ### R6. `mul_zero`, `Real.exp_zero` · goal: `rexp (-x * 0)` → `1`
`mul_zero a : a * 0 = 0`, `Real.exp_zero : rexp 0 = 1`. -/
example (x : ℝ) (P : ℝ → Prop) (h : P 1) : P (rexp (-x * 0)) := by
  simp only [mul_zero, Real.exp_zero]
  exact h

/-! ### R7. `zero_mul`, `zero_add` · goal: `0 * u + v` → `v` (a term with energy `0` drops out)
`zero_mul a : 0 * a = 0`, `zero_add a : 0 + a = a`. -/
example (u v : ℝ) (P : ℝ → Prop) (h : P v) : P (0 * u + v) := by
  simp only [zero_mul, zero_add]
  exact h

/-! ### R8. `neg_mul` · `-a * b = -(a * b)` · goal: the sign moves out of the product -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (-(a * b))) : P (-a * b) := by
  rw [neg_mul]
  exact h

/-! ## Algebra with exponentials -/

/-! ### R9. `Real.exp_neg` · `rexp (-y) = (rexp y)⁻¹` · goal -/
example (y : ℝ) (P : ℝ → Prop) (h : P (rexp y)⁻¹) : P (rexp (-y)) := by
  rw [Real.exp_neg]
  exact h

/-! ### R10. `field_simp` · goal: clears the fractions (multiplies through by denominators) and,
for an equation, usually closes it. It must know each denominator is `≠ 0`: it finds this itself for
`rexp y` (always `> 0`) and for numerals, and uses hypotheses such as `hx : 0 < x`. -/
example (a x : ℝ) (hx : 0 < x) (P : ℝ → Prop) (h : P (a * x / (x + 1))) : P (a / (1 + x⁻¹)) := by
  field_simp
  exact h

/-! ## Replacing a function by a closed form -/

/-! ### R11. `funext h` · context gains `f = g` from `h : ∀ y, f y = g y`
Two functions are equal when they agree at every point (function extensionality). -/
example (f g : ℝ → ℝ) (h : ∀ y, f y = g y) (G : Prop) (k : f = g → G) : G := by
  have hfg := funext h
  exact k hfg

/-! ### R12. `rw [show f = g from e]` · goal: `P f` → `P g`
`show T from e` is the term `e` with its type written out as `T`; `rw` then rewrites with it. Use it
when `f` appears unapplied (`Tendsto f …`), where `rw [h]` with `h : ∀ y, f y = …` finds no `f y`. -/
example (f : ℝ → ℝ) (c : ℝ) (h : ∀ y, f y = c * y) (P : (ℝ → ℝ) → Prop) (k : P (fun y => c * y)) :
    P f := by
  rw [show f = fun y => c * y from funext h]
  exact k

/-! ## Limits: `Tendsto f l l'` -/

/-! ### R13. `apply Tendsto.div_atTop hf` · goal: `f / g → 0` → `g → ∞`
`Tendsto.div_atTop : Tendsto f l (𝓝 a) → Tendsto g l atTop → Tendsto (fun x => f x / g x) l (𝓝 0)`:
a convergent numerator over a denominator that grows without bound tends to `0`. -/
example {α : Type} (l : Filter α) (f g : α → ℝ) (a : ℝ) (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l atTop) : Tendsto (fun y => f y / g y) l (𝓝 0) := by
  apply Tendsto.div_atTop hf
  exact hg

/-! ### R14. `tendsto_const_nhds` · closes `Tendsto (fun _ => c) l (𝓝 c)`: a constant tends to itself -/
example {α : Type} (l : Filter α) (c : ℝ) : Tendsto (fun _ : α => c) l (𝓝 c) := by
  exact tendsto_const_nhds

/-! ### R15. `Real.tendsto_exp_atTop` · context gains `Tendsto rexp atTop atTop` (`eˣ → ∞` as `x → ∞`) -/
example (G : Prop) (k : Tendsto rexp atTop atTop → G) : G := by
  have he := Real.tendsto_exp_atTop
  exact k he

/-! ### R16. `tendsto_id` · context gains `Tendsto id l l` (`y → ∞` as `y → ∞`, for `l = atTop`) -/
example (G : Prop) (k : Tendsto (id : ℝ → ℝ) atTop atTop → G) : G := by
  have hi : Tendsto (id : ℝ → ℝ) atTop atTop := tendsto_id
  exact k hi

/-! ### R17. `hf.atTop_mul_const hr` (`Tendsto.atTop_mul_const`) · context gains `f * r → ∞`
`hr : 0 < r` and `hf : Tendsto f l atTop` give `Tendsto (fun y => f y * r) l atTop`. -/
example {α : Type} (l : Filter α) (f : α → ℝ) (r : ℝ) (hr : 0 < r) (hf : Tendsto f l atTop)
    (G : Prop) (k : Tendsto (fun y => f y * r) l atTop → G) : G := by
  have hm := hf.atTop_mul_const hr
  exact k hm

/-! ### R18. `hg.comp hf` (`Tendsto.comp`) · context gains the limit of `g ∘ f`
`hg : Tendsto g l' l''` and `hf : Tendsto f l l'` give `Tendsto (g ∘ f) l l''`: if `f → ∞` and
`g(t) → ∞` as `t → ∞`, then `g (f y) → ∞`. -/
example (f g : ℝ → ℝ) (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) (G : Prop)
    (k : Tendsto (g ∘ f) atTop atTop → G) : G := by
  have hc := hg.comp hf
  exact k hc

/-! ### R19. `hf.atTop_add hg` (`Tendsto.atTop_add`) · context gains `f + g → ∞`
`hf : Tendsto f l atTop` and `hg : Tendsto g l (𝓝 C)` give `Tendsto (fun y => f y + g y) l atTop`. -/
example {α : Type} (l : Filter α) (f g : α → ℝ) (C : ℝ) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) (G : Prop) (k : Tendsto (fun y => f y + g y) l atTop → G) : G := by
  have hs := hf.atTop_add hg
  exact k hs

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The ground-state probability of `twoState a b` in closed form: R2, R3, R4, R5 -/
example (a b x : ℝ) :
    (twoState a b).probabilityBetaReal x 0 = rexp (-x * a) / (rexp (-x * a) + rexp (-x * b)) := by
  simp only [probabilityBetaReal, mathematicalPartitionFunctionBetaReal, Fin.sum_univ_two,
    twoState_energy_fst, twoState_energy_snd]

/-! ### W2. Swapping a function for its closed form, then a limit: R11 → R12, R16, R17
`rw [h]` fails here: the goal mentions `f` but never `f y`. -/
example (f : ℝ → ℝ) (h : ∀ y, f y = y * 3) : Tendsto f atTop atTop := by
  rw [show f = fun y => y * 3 from funext h]
  exact tendsto_id.atTop_mul_const (by norm_num)

/-! ### W3. `y ↦ e^{2y}` grows without bound: R15, R16 → R17 → R18
The composite `hc` is about `rexp ∘ fun x => id x * 2`; `exact hc` still closes the goal about
`fun y => rexp (y * 2)`, because both unfold to the same function (they are definitionally equal). -/
example : Tendsto (fun y : ℝ => rexp (y * 2)) atTop atTop := by
  have hc := Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 2))
  exact hc

/-! ### W4. A constant over something that grows tends to `0`: R13, R14, then R19 with R14 -/
example (c r : ℝ) (hr : 0 < r) : Tendsto (fun y : ℝ => c / (y * r + 7)) atTop (𝓝 0) := by
  apply Tendsto.div_atTop tendsto_const_nhds
  exact (tendsto_id.atTop_mul_const hr).atTop_add tendsto_const_nhds

end M156Guide
