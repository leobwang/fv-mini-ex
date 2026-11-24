/- Guide for M158 (Maximum entropy).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (two points, `1/3`, other numbers).
Assumed: Lean basics.
-/
import Mathlib

open Real

namespace M158Guide

/-! # Part R · Reference entries -/

/-! ## Naming the number of states and proving it is positive -/

/-! ### R1. `set x : T := e with hx` · context gains `x := e` and `hx : x = e`; goal: `e` → `x` -/
example (k : ℕ) (P : ℝ → Prop) (h : ∀ x : ℝ, P x) : P (k : ℝ) := by
  set x : ℝ := (k : ℝ) with hx
  exact h x

/-! ### R2. `Fintype.card_pos` · closes `0 < Fintype.card α` (needs `[Nonempty α]`) -/
example {α : Type} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by
  exact Fintype.card_pos

/-! ### R3. `exact_mod_cast h` · closes a goal that is `h` up to casts `ℕ → ℝ` -/
example (k : ℕ) (h : 0 < k) : (0 : ℝ) < k := by
  exact_mod_cast h

/-! ## Jensen's inequality for a concave function -/

/-! ### R4. `Real.concaveOn_negMulLog` · context gains `ConcaveOn ℝ (Set.Ici 0) negMulLog` -/
example (G : Prop) (g : ConcaveOn ℝ (Set.Ici 0) Real.negMulLog → G) : G := by
  have hc := Real.concaveOn_negMulLog
  exact g hc

/-! ### R5. `ConcaveOn.le_map_sum` (Jensen) with named arguments `(t := …) (w := …) (p := …)`
· context gains the inequality; goal list gains its three side conditions (one per `?_`) -/
example {ι : Type} (s : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ s f) (t : Finset ι) (w p : ι → ℝ)
    (G : Prop) (g : ∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i) → G)
    (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) (hm : ∀ i ∈ t, p i ∈ s) : G := by
  have hJ := hf.le_map_sum (t := t) (w := w) (p := p) ?_ ?_ ?_
  exacts [g hJ, h0, h1, hm]

/-! ### R6. `positivity` · closes `0 ≤ e` / `0 < e` for `e` built from casts, `/`, `*`, … -/
example (k : ℕ) : (0 : ℝ) ≤ 1 / (k : ℝ) := by
  positivity

/-! ### R7. `Finset.sum_const` · `∑ _x ∈ s, b = s.card • b` · goal: sum of a constant → `card • b` -/
example {ι : Type} (t : Finset ι) (b : ℝ) (P : ℝ → Prop) (h : P (t.card • b)) :
    P (∑ _i ∈ t, b) := by
  rw [Finset.sum_const]
  exact h

/-! ### R8. `Finset.card_univ` · `Finset.univ.card = Fintype.card α` · goal -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) :
    P (Finset.univ : Finset α).card := by
  rw [Finset.card_univ]
  exact h

/-! ### R9. `nsmul_eq_mul` · `k • a = ↑k * a` · goal: `ℕ`-scalar → product in the ring -/
example (k : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (↑k * a)) : P (k • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R10. `Set.mem_Ici` · `x ∈ Set.Ici a ↔ a ≤ x` · goal: membership → inequality
`Set.Ici a` is the interval `[a, ∞)`. The two sides are equal by definition, so `exact hx` with
`hx : a ≤ x` also works without the `rw`. -/
example (a x : ℝ) (hx : a ≤ x) : x ∈ Set.Ici a := by
  rw [Set.mem_Ici]
  exact hx

/-! ## Simplifying Jensen's inequality -/

/-! ### R11. `smul_eq_mul` · `a • b = a * b` in a ring · goal, also under `∑` with `simp only` -/
example {ι : Type} (t : Finset ι) (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P (∑ i ∈ t, a * f i)) :
    P (∑ i ∈ t, a • f i) := by
  simp only [smul_eq_mul]
  exact h

/-! ### R12. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `←` pulls a constant out -/
example {ι : Type} (t : Finset ι) (a : ℝ) (f : ι → ℝ) (P : ℝ → Prop) (h : P (a * ∑ i ∈ t, f i)) :
    P (∑ i ∈ t, a * f i) := by
  simp only [← Finset.mul_sum]
  exact h

/-! ## Evaluating `negMulLog` at `1/n` -/

/-! ### R13. `Real.negMulLog` · `negMulLog x = -x * log x` · goal: unfold the definition
The infoview prints `Real.negMulLog x` as `x.negMulLog`. -/
example (x : ℝ) (P : ℝ → Prop) (h : P (-x * log x)) : P (Real.negMulLog x) := by
  simp only [Real.negMulLog]
  exact h

/-! ### R14. `one_div` · `1 / a = a⁻¹` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a⁻¹) : P (1 / a) := by
  rw [one_div]
  exact h

/-! ### R15. `Real.log_inv` · `log x⁻¹ = -log x` (for every real `x`) · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P (-log x)) : P (log x⁻¹) := by
  rw [Real.log_inv]
  exact h

/-! ### R16. `field_simp` · clears denominators; closes `a⁻¹ * b = b / a` -/
example (a b : ℝ) (ha : a ≠ 0) : a⁻¹ * b = b / a := by
  field_simp

/-! ## Multiplying an inequality by a positive number -/

/-! ### R17. `ha.le` (`LT.lt.le`) · context gains `0 ≤ a` from `ha : 0 < a` -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (g : 0 ≤ a → G) : G := by
  have ha' := ha.le
  exact g ha'

/-! ### R18. `mul_le_mul_of_nonneg_left` · `b ≤ c → 0 ≤ a → a * b ≤ a * c` · context gains it -/
example (a b c : ℝ) (h : b ≤ c) (ha : 0 ≤ a) (G : Prop) (g : a * b ≤ a * c → G) : G := by
  have h2 := mul_le_mul_of_nonneg_left h ha
  exact g h2

/-! ### R19. `ha.ne'` (`LT.lt.ne'`) · context gains `a ≠ 0` from `ha : 0 < a` -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (g : a ≠ 0 → G) : G := by
  have ha' := ha.ne'
  exact g ha'

/-! ### R20. `mul_assoc` · `a * b * c = a * (b * c)`; `←` regroups to the left · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * b * c)) : P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R21. `mul_one_div_cancel` · `a ≠ 0 → a * (1 / a) = 1` · goal -/
example (a : ℝ) (ha : a ≠ 0) (P : ℝ → Prop) (h : P 1) : P (a * (1 / a)) := by
  rw [mul_one_div_cancel ha]
  exact h

/-! ### R22. `one_mul` · `1 * a = a` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R23. `mul_div_cancel₀` · `(b : G₀) → a ≠ 0 → a * (b / a) = b` · goal -/
example (a b : ℝ) (ha : a ≠ 0) (P : ℝ → Prop) (h : P b) : P (a * (b / a)) := by
  rw [mul_div_cancel₀ b ha]
  exact h

/-! ### R24. `rwa [e] at h` · rewrites hypothesis `h`, then closes the goal with it -/
example (a b : ℝ) (e : a = b) (P : ℝ → Prop) (h : P a) : P b := by
  rwa [e] at h

/-! ## The uniform distribution -/

/-! ### R25. `mul_inv_cancel_left₀` · `a ≠ 0 → a * (a⁻¹ * b) = b` · goal (`simp` finds it) -/
example (a b : ℝ) (ha : a ≠ 0) (P : ℝ → Prop) (h : P b) : P (a * (a⁻¹ * b)) := by
  rw [mul_inv_cancel_left₀ ha]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Jensen with two equal weights `1/2` on `Fin 2`: R5 with R6, `simp`, `simpa`; then R11 -/
example (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 / 2 : ℝ) * f x + (1 / 2) * f y ≤ f ((1 / 2) * x + (1 / 2) * y) := by
  have hJ := hf.le_map_sum (t := Finset.univ) (w := fun _ : Fin 2 => (1 / 2 : ℝ)) (p := ![x, y])
    (fun _ _ => by positivity) (by simp) (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using hJ

/-! ### W2. A sum of a constant over a finite type: R7, R8, R9 inside one `simp` -/
example {α : Type} [Fintype α] (b : ℝ) : ∑ _i : α, b = Fintype.card α * b := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### W3. `negMulLog` at `1/3`: R13, R14, R15 inside `simp`, then R16 -/
example : Real.negMulLog (1 / 3) = Real.log 3 / 3 := by
  simp [Real.negMulLog, Real.log_inv]
  field_simp

/-! ### W4. Undo a factor `1/a` on the left and `/a` on the right: R18 with R17, then R24 with
R20, R21, R22, R23 -/
example (a x y : ℝ) (ha : 0 < a) (h : 1 / a * x ≤ y / a) : x ≤ y := by
  have h2 := mul_le_mul_of_nonneg_left h ha.le
  rwa [← mul_assoc, mul_one_div_cancel ha.ne', one_mul, mul_div_cancel₀ _ ha.ne'] at h2

end M158Guide
