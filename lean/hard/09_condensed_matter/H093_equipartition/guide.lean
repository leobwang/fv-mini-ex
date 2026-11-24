/- Guide for H093 (Equipartition).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` with `g : … → G` is an arbitrary goal for entries that only add a fact to the context.
Part W: worked combinations on objects that are NOT the exercise's (the Gaussian itself, `Γ(5/2)`,
`a ^ (-5/2)`, a quartic toy ensemble).
Infoview: `rexp` is `Real.exp`; `√x` is `Real.sqrt x`; `∫ x, f x` is the Lebesgue integral over ℝ;
`x ^ 2` may be a NATURAL power or a REAL power `x ^ (2 : ℝ)` (they print the same, R2).
Assumed: Lean basics (E001–E033).
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

open CanonicalEnsemble Constants Real MeasureTheory

namespace H093Guide

/-- A toy ensemble used below (not the exercise's): states `x : ℝ`, energy `c x⁴`, Lebesgue measure. -/
noncomputable def quartic (c : ℝ) : CanonicalEnsemble ℝ where
  energy x := c * x ^ 4
  dof := 1
  energy_measurable := (by fun_prop)

/-! # Part R · Reference entries -/

/-! ## Even integrands: from `ℝ` to the half-line `(0, ∞)` -/

/-! ### R1. `integral_comp_abs` · `∫ x, f |x| = 2 * ∫ x in Set.Ioi 0, f x`; `rw [← integral_comp_abs]` · goal
Name the function with `(f := fun x => …)` when Lean cannot guess it from the goal. -/
example (f : ℝ → ℝ) (P : ℝ → Prop) (h : P (∫ x, f |x|)) : P (2 * ∫ x in Set.Ioi 0, f x) := by
  rw [← integral_comp_abs]
  exact h

/-! ### R2. `Real.rpow_two` · `x ^ (2 : ℝ) = x ^ 2` (real power → natural power) · goal
Both sides PRINT as `x ^ 2`; the left one is `Real.rpow`, the exponent a real number. -/
example (x : ℝ) (P : ℝ → Prop) (h : P (x ^ (2 : ℕ))) : P (x ^ (2 : ℝ)) := by
  rw [Real.rpow_two]
  exact h

/-! ### R3. `sq_abs` · `|a| ^ 2 = a ^ 2` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P (a ^ 2)) : P (|a| ^ 2) := by
  rw [sq_abs]
  exact h

/-! ## Gaussian and Gamma integrals -/

/-! ### R4. `integral_rpow_mul_exp_neg_mul_rpow` · the Gamma formula on `(0, ∞)` · goal
`0 < p → -1 < q → 0 < b → ∫ x in Ioi 0, x ^ q * rexp (-b * x ^ p) = b ^ (-(q+1)/p) * (1/p) * Γ((q+1)/p)`,
all powers real (`rpow`). -/
example (p q b : ℝ) (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) (P : ℝ → Prop)
    (h : P (b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p))) :
    P (∫ x in Set.Ioi 0, x ^ q * rexp (-b * x ^ p)) := by
  rw [integral_rpow_mul_exp_neg_mul_rpow hp hq hb]
  exact h

/-! ### R5. `integral_gaussian` · `∫ x, rexp (-b * x ^ 2) = √(π / b)` (natural power `^ 2`) · goal -/
example (b : ℝ) (P : ℝ → Prop) (h : P √(π / b)) : P (∫ x : ℝ, rexp (-b * x ^ 2)) := by
  rw [integral_gaussian]
  exact h

/-! ### R6. `rw [show A = B by norm_num]` · goal: a numeral expression `A` → the form `B` a lemma needs -/
example (f : ℝ → ℝ) (P : ℝ → Prop) (h : P (f (3 / 2 + 1))) : P (f ((4 + 1) / 2)) := by
  rw [show ((4 : ℝ) + 1) / 2 = 3 / 2 + 1 by norm_num]
  exact h

/-! ### R7. `Real.Gamma_add_one` · `s ≠ 0 → Γ(s + 1) = s * Γ(s)` · goal
`rw [Real.Gamma_add_one (by norm_num)]` proves `s ≠ 0` on the spot for a numeral `s`. -/
example (s : ℝ) (hs : s ≠ 0) (P : ℝ → Prop) (h : P (s * Gamma s)) : P (Gamma (s + 1)) := by
  rw [Real.Gamma_add_one hs]
  exact h

/-! ### R8. `Real.Gamma_one_half_eq` · `Γ(1/2) = √π` · goal -/
example (P : ℝ → Prop) (h : P √π) : P (Gamma (1 / 2)) := by
  rw [Real.Gamma_one_half_eq]
  exact h

/-! ## Real powers `a ^ (y : ℝ)` and square roots -/

/-! ### R9. `Real.rpow_neg` · `0 ≤ x → x ^ (-y) = (x ^ y)⁻¹` · goal
From `ha : 0 < a`, `ha.le : 0 ≤ a` is the weak inequality (`LT.lt.le`). -/
example (a y : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P (a ^ y)⁻¹) : P (a ^ (-y)) := by
  rw [Real.rpow_neg ha.le]
  exact h

/-! ### R10. `Real.rpow_add` · `0 < x → x ^ (y + z) = x ^ y * x ^ z` · goal -/
example (a y z : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P (a ^ y * a ^ z)) : P (a ^ (y + z)) := by
  rw [Real.rpow_add ha]
  exact h

/-! ### R11. `Real.rpow_one` · `x ^ (1 : ℝ) = x` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a ^ (1 : ℝ)) := by
  rw [Real.rpow_one]
  exact h

/-! ### R12. `Real.sqrt_eq_rpow` · `√x = x ^ (1 / 2)`; `rw [← Real.sqrt_eq_rpow]` · goal: `x ^ (1/2)` → `√x` -/
example (a : ℝ) (P : ℝ → Prop) (h : P √a) : P (a ^ (1 / 2 : ℝ)) := by
  rw [← Real.sqrt_eq_rpow]
  exact h

/-! ### R13. `Real.sqrt_pos` · `0 < √x ↔ 0 < x`; `.mpr` · context gains `0 < √a` -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (g : 0 < √a → G) : G := by
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  exact g hsa

/-! ### R14. `Real.sqrt_div'` · `0 ≤ y → √(x / y) = √x / √y` · goal
`Real.sqrt_div' x hy`; write `_` for `x` and let `rw` find it. -/
example (x a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P (√x / √a)) : P √(x / a) := by
  rw [Real.sqrt_div' _ ha.le]
  exact h

/-! ### R15. `field_simp` · closes (or simplifies) an equation of fractions
It multiplies out every denominator it can prove `≠ 0` (from `0 < d` or `d ≠ 0` in the context, or
numerals), then normalises both sides with `ring_nf`; equal normal forms close the goal. -/
example (a s : ℝ) (ha : 0 < a) (hs : 0 < s) : 3 * (1 / (a * s) * (1 / 3)) = 1 / a * (1 / s) := by
  field_simp

/-! ## Equations of functions and structure fields -/

/-! ### R16. `funext x` · goal `f = g` (functions) → `f x = g x`; context gains `x` -/
example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R17. `simp only [D]` on a structure built with `where` · goal: `(D c).field` → that field's body -/
example (c x : ℝ) (P : ℝ → Prop) (h : P (c * x ^ 4)) : P ((quartic c).energy x) := by
  simp only [quartic]
  exact h

/-! ### R18. `ring_nf` · closes `f A = f B` when `A` and `B` are equal as ring expressions
`ring_nf` normalises every ring subexpression, also inside `rexp (…)`. -/
example (b c x : ℝ) : c * x ^ 4 * rexp (-b * (c * x ^ 4)) = c * (x ^ 4 * rexp (-(b * c) * x ^ 4)) := by
  ring_nf

/-! ## The mean energy -/

/-! ### R19. `CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals` · goal: `⟨E⟩` → a ratio of integrals -/
example {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (P : ℝ → Prop)
    (h : P ((∫ i, 𝓒.energy i * rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ) /
      ∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ)) :
    P (𝓒.meanEnergy T) := by
  rw [meanEnergy_eq_ratio_of_integrals]
  exact h

/-! ### R20. `Temperature.beta_pos` · `0 < T.val → 0 < (T.β : ℝ)` · context gains `hβ` -/
example (T : Temperature) (hT : 0 < T.val) (G : Prop) (g : 0 < (T.β : ℝ) → G) : G := by
  have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT
  exact g hβ

/-! ### R21. `positivity` · closes `0 < e` / `0 ≤ e` for `e` built from `*`, `/`, `√`, `π`, numerals and
atoms `a` with `0 < a` in the context -/
example (b c : ℝ) (hb : 0 < b) (hc : 0 < c) : 0 < √(π / (b * c / 2)) := by
  positivity

/-! ### R22. `show G'` · goal: replaced by a definitionally equal goal (here `∂(D c).μ` → `∂volume`)
`_` in `G'` stands for the part you do not want to retype. The measure field `μ` was not given in
`quartic`, so it is the default `volume`, by definition. -/
example (c : ℝ) (f : ℝ → ℝ) (y : ℝ) (h : ∫ x, f x ∂volume = y) : ∫ x, f x ∂(quartic c).μ = y := by
  show ∫ x, f x ∂volume = _
  exact h

/-! ### R23. `rw [hfg]` with an equation of FUNCTIONS · goal: the integrand `fun x => …` replaced whole
`∫ x, B x` is `integral volume (fun x => B x)`: the integrand is a literal `fun`, so an equation
`hfg : (fun x => B x) = fun x => C x` rewrites it, although `rw` cannot use `∀ x, B x = C x` under `∫`. -/
example (c : ℝ) (hfg : (fun x : ℝ => c * x ^ 4) = fun x => x ^ 4 * c) (P : ℝ → Prop)
    (h : P (∫ x, x ^ 4 * c)) : P (∫ x, c * x ^ 4) := by
  rw [hfg]
  exact h

/-! ### R24. `integral_const_mul` · `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ` · goal: a constant factor out -/
example (r : ℝ) (f : ℝ → ℝ) (P : ℝ → Prop) (h : P (r * ∫ x, f x)) : P (∫ x, r * f x) := by
  rw [integral_const_mul]
  exact h

/-! ## Cancelling the partition function -/

/-! ### R25. `mul_assoc` · `a * b * c = a * (b * c)`; `rw [← mul_assoc]` regroups to the left · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * b * c)) : P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R26. `mul_div_assoc` · `a * b / c = a * (b / c)` · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * (b / c))) : P (a * b / c) := by
  rw [mul_div_assoc]
  exact h

/-! ### R27. `div_self` · `a ≠ 0 → a / a = 1` · goal
From `hZ : 0 < Z`, `hZ.ne' : Z ≠ 0` (`ne'` flips `0 ≠ Z` to `Z ≠ 0`). -/
example (Z : ℝ) (hZ : 0 < Z) (P : ℝ → Prop) (h : P 1) : P (Z / Z) := by
  rw [div_self hZ.ne']
  exact h

/-! ### R28. `mul_one` · `a * 1 = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ## Temperature and Boltzmann's constant -/

/-! ### R29. `Temperature.β_toReal` · `(T.β : ℝ) = 1 / (kB * T.toReal)` · goal -/
example (T : Temperature) (P : ℝ → Prop) (h : P (1 / (kB * T.toReal))) : P (T.β : ℝ) := by
  rw [Temperature.β_toReal]
  exact h

/-! ### R30. `have h : (0 : ℝ) < T.toReal := hT` · context: `0 < T.val` (in `ℝ≥0`) restated in `ℝ`
`T.toReal` is `↑T.val` by definition, and `<` on `ℝ≥0` is `<` of the casts, so `hT` itself is the proof. -/
example (T : Temperature) (hT : 0 < T.val) (G : Prop) (g : (0 : ℝ) < T.toReal → G) : G := by
  have hT' : (0 : ℝ) < T.toReal := hT
  exact g hT'

/-! ### R31. `Constants.kB_pos` · `0 < kB` · context gains `this : 0 < kB` -/
example (G : Prop) (g : 0 < kB → G) : G := by
  have := kB_pos
  exact g this

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The Gaussian itself, folded onto the half-line: R1 with `(f := …)`, then R2, R3 -/
example (b : ℝ) :
    ∫ x : ℝ, rexp (-b * x ^ 2) = 2 * ∫ x in Set.Ioi 0, rexp (-b * x ^ (2 : ℝ)) := by
  rw [← integral_comp_abs (f := fun x : ℝ => rexp (-b * x ^ (2 : ℝ)))]
  simp only [Real.rpow_two, sq_abs]

/-! ### W2. `Γ(5/2) = (3/4)√π`: R6, R7 twice, R8, then `ring` -/
example : Gamma ((4 + 1) / 2) = 3 / 4 * √π := by
  rw [show ((4 : ℝ) + 1) / 2 = 3 / 2 + 1 by norm_num]
  rw [Real.Gamma_add_one (by norm_num)]
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num]
  rw [Real.Gamma_add_one (by norm_num)]
  rw [Real.Gamma_one_half_eq]
  ring

/-! ### W3. `a ^ (-5/2) = 1 / (a * a * √a)`: R6, R9, R10 twice, R11, R12, then `ring` -/
example (a : ℝ) (ha : 0 < a) : a ^ (-((4 : ℝ) + 1) / 2) = 1 / (a * a * √a) := by
  rw [show -((4 : ℝ) + 1) / 2 = -(1 + 1 + 1 / 2) by norm_num]
  rw [Real.rpow_neg ha.le]
  rw [Real.rpow_add ha, Real.rpow_add ha, Real.rpow_one]
  rw [← Real.sqrt_eq_rpow]
  ring

/-! ### W4. Cancelling a common positive factor `Z`: R25, R26, R27, R28 -/
example (c d Z : ℝ) (hZ : 0 < Z) : c * (d * Z) / Z = c * d := by
  rw [← mul_assoc]
  rw [mul_div_assoc]
  rw [div_self hZ.ne']
  rw [mul_one]

/-! ### W5. The quartic toy ensemble: R19, then R22 to switch the measure to `volume` -/
example (c : ℝ) (T : Temperature) (y : ℝ)
    (h : (∫ x, (quartic c).energy x * rexp (-↑T.β * (quartic c).energy x) ∂volume) /
      (∫ x, rexp (-↑T.β * (quartic c).energy x) ∂volume) = y) :
    (quartic c).meanEnergy T = y := by
  rw [meanEnergy_eq_ratio_of_integrals]
  show (∫ x, (quartic c).energy x * rexp (-↑T.β * (quartic c).energy x) ∂volume) /
    (∫ x, rexp (-↑T.β * (quartic c).energy x) ∂volume) = _
  exact h

end H093Guide
