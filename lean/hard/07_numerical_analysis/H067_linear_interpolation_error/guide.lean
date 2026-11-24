/- Guide for H067 (Linear interpolation error).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G : Prop`
is an arbitrary goal, and a hypothesis `k : … → G` is only there to consume the new fact, so the entry
shows what entered the context. A hypothesis `h` that finishes an example shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the parabola `(t - 1)(t - 3)`, `[1, 3]`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H067Guide

/-! # Part R · Reference entries -/

/-! ## Derivative arithmetic (milestone `aux_deriv`) -/

/-! ### R1. `hasDerivAt_id' x` · context gains `HasDerivAt (fun x => x) 1 x` (slope of `y ↦ y`) -/
example (x : ℝ) (G : Prop) (k : HasDerivAt (fun y => y) 1 x → G) : G := by
  have hid := hasDerivAt_id' x
  exact k hid

/-! ### R2. `HasDerivAt.sub_const` · `HasDerivAt g d x → HasDerivAt (fun y => g y - c) d x` · context -/
example (g : ℝ → ℝ) (d c x : ℝ) (hg : HasDerivAt g d x) (G : Prop)
    (k : HasDerivAt (fun y => g y - c) d x → G) : G := by
  have h2 := hg.sub_const c
  exact k h2

/-! ### R3. `HasDerivAt.const_mul` · `HasDerivAt g d x → HasDerivAt (fun y => c * g y) (c * d) x` · context -/
example (g : ℝ → ℝ) (d c x : ℝ) (hg : HasDerivAt g d x) (G : Prop)
    (k : HasDerivAt (fun y => c * g y) (c * d) x → G) : G := by
  have h3 := hg.const_mul c
  exact k h3

/-! ### R4. `HasDerivAt.const_add` · `HasDerivAt g d x → HasDerivAt (fun y => c + g y) d x` · context -/
example (g : ℝ → ℝ) (d c x : ℝ) (hg : HasDerivAt g d x) (G : Prop)
    (k : HasDerivAt (fun y => c + g y) d x → G) : G := by
  have h4 := hg.const_add c
  exact k h4

/-! ### R5. `HasDerivAt.mul` · product rule: `HasDerivAt (g * l) (d * l x + g x * e) x` · context
`g * l` is the pointwise product `fun y => g y * l y`. -/
example (g l : ℝ → ℝ) (d e x : ℝ) (hg : HasDerivAt g d x) (hl : HasDerivAt l e x) (G : Prop)
    (k : HasDerivAt (fun y => g y * l y) (d * l x + g x * e) x → G) : G := by
  have h5 := hg.mul hl
  exact k h5

/-! ### R6. `HasDerivAt.sub` · `HasDerivAt g d x → HasDerivAt l e x → HasDerivAt (fun y => g y - l y) (d - e) x` -/
example (g l : ℝ → ℝ) (d e x : ℝ) (hg : HasDerivAt g d x) (hl : HasDerivAt l e x) (G : Prop)
    (k : HasDerivAt (fun y => g y - l y) (d - e) x → G) : G := by
  have h6 := hg.sub hl
  exact k h6

/-! ### R7. `HasDerivAt.congr_deriv` · goal `HasDerivAt g e x` → `d = e`, given `hg : HasDerivAt g d x`
The derivative R1–R6 build is never in the shape you want; this trades it for an equation (`ring`). -/
example (g : ℝ → ℝ) (d e x : ℝ) (hg : HasDerivAt g d x) (hde : d = e) : HasDerivAt g e x := by
  refine hg.congr_deriv ?_
  exact hde

/-! ## Naming, nonzero denominators, continuity (milestone `interp_error_eq`) -/

/-! ### R8. `set k := e with hk` · goal and context: `e` is renamed `k` everywhere; `hk : k = e` -/
example (u v : ℝ) (P : ℝ → Prop) (h : P (u / v)) : P (u / v) := by
  set k := u / v with hk
  exact h

/-! ### R9. `mul_ne_zero` · `a ≠ 0 → b ≠ 0 → a * b ≠ 0` · goal list: one goal per factor -/
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  apply mul_ne_zero
  exact ha
  exact hb

/-! ### R10. `linarith` · closes `<`, `≤`, `=`, and also `≠` goals that follow linearly from hypotheses -/
example (a x : ℝ) (h : a < x) : x - a ≠ 0 := by
  linarith

/-! ### R11. `continuous_iff_continuousAt` · goal `Continuous g` → `∀ x, ContinuousAt g x`
In a term, `continuous_iff_continuousAt.mpr (fun t => …)`. -/
example (g : ℝ → ℝ) (h : ∀ x, ContinuousAt g x) : Continuous g := by
  rw [continuous_iff_continuousAt]
  exact h

/-! ### R12. `HasDerivAt.continuousAt` · `HasDerivAt g d x → ContinuousAt g x` · context -/
example (g : ℝ → ℝ) (d x : ℝ) (hg : HasDerivAt g d x) (G : Prop) (k : ContinuousAt g x → G) : G := by
  have hc := hg.continuousAt
  exact k hc

/-! ### R13. `div_mul_cancel₀` · `b ≠ 0 → a / b * b = a` · goal (here `rw`, with `hb` given) -/
example (a b : ℝ) (hb : b ≠ 0) (P : ℝ → Prop) (h : P a) : P (a / b * b) := by
  rw [div_mul_cancel₀ a hb]
  exact h

/-! ### R14. `simp only [k]` · goal: unfold a name made by `set`, and apply the `fun` (β-reduction) -/
example (g : ℝ → ℝ) (c y : ℝ) (P : ℝ → Prop) (h : P (g y - c * y)) : P ((fun t => g t - c * t) y) := by
  set k := fun t => g t - c * t with hk
  simp only [k]
  exact h

/-! ### R15. `linear_combination e` · closes `lhs = rhs` when `lhs - rhs` equals `e.lhs - e.rhs` by `ring`
`e` is a proof of an equation, possibly scaled: `linear_combination -h`, `linear_combination 2 * h`. -/
example (u v w : ℝ) (h : u * v = w) : w - u * v + 0 = 0 := by
  linear_combination -h

/-! ## Rolle's theorem and its hypotheses -/

/-! ### R16. `exists_hasDerivAt_eq_zero` · Rolle: `a < b → ContinuousOn g (Icc a b) → g a = g b →
(∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) → ∃ c ∈ Ioo a b, g' c = 0` · context -/
example (g g' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hc : ContinuousOn g (Set.Icc a b)) (he : g a = g b)
    (hd : ∀ x, HasDerivAt g (g' x) x) (G : Prop) (k : (∃ c ∈ Set.Ioo a b, g' c = 0) → G) : G := by
  have hr := exists_hasDerivAt_eq_zero hab hc he fun x _ => hd x
  exact k hr

/-! ### R17. `Continuous.continuousOn` · `Continuous g → ContinuousOn g s` · context -/
example (g : ℝ → ℝ) (s : Set ℝ) (hg : Continuous g) (G : Prop) (k : ContinuousOn g s → G) : G := by
  have hs := hg.continuousOn (s := s)
  exact k hs

/-! ### R18. `h₁.trans h₂.symm` (`Eq.trans`, `Eq.symm`) · `u = 0 → v = 0 → u = v` · context -/
example (u v : ℝ) (h₁ : u = 0) (h₂ : v = 0) (G : Prop) (k : u = v → G) : G := by
  have he := h₁.trans h₂.symm
  exact k he

/-! ### R19. `obtain ⟨c, hc, h⟩ := hr` · context: `hr : ∃ c ∈ s, Q c` → a point, its membership, its property -/
example (s : Set ℝ) (Q : ℝ → Prop) (hr : ∃ c ∈ s, Q c) (G : Prop) (k : ∀ c ∈ s, Q c → G) : G := by
  obtain ⟨c, hc, h⟩ := hr
  exact k c hc h

/-! ### R20. `hc.1`, `hc.2` · `hc : c ∈ Set.Ioo a b` IS `a < c ∧ c < b` · context gains a part -/
example (a b c : ℝ) (hc : c ∈ Set.Ioo a b) (G : Prop) (k : c < b → G) : G := by
  have h2 := hc.2
  exact k h2

/-! ### R21. `h₁.trans h₂` (`LT.lt.trans`) · `a < b → b < c → a < c` · context -/
example (a b c : ℝ) (h₁ : a < b) (h₂ : b < c) (G : Prop) (k : a < c → G) : G := by
  have h3 := h₁.trans h₂
  exact k h3

/-! ### R22. `refine ⟨c, ⟨h₁, h₂⟩, ?_⟩` · goal `∃ x ∈ Ioo a b, Q x` → `Q c` (point and membership given) -/
example (a b c : ℝ) (Q : ℝ → Prop) (h₁ : a < c) (h₂ : c < b) (hQ : Q c) : ∃ x ∈ Set.Ioo a b, Q x := by
  refine ⟨c, ⟨h₁, h₂⟩, ?_⟩
  exact hQ

/-! ### R23. `rw [show u = v by tac]` · goal: rewrite with a fact proved on the spot -/
example (u w : ℝ) (h : u - w = 0) (P : ℝ → Prop) (hP : P w) : P u := by
  rw [show u = w by linarith]
  exact hP

/-! ### R24. `mul_div_cancel_left₀` · `a ≠ 0 → a * b / a = b`; with `two_ne_zero : (2 : ℝ) ≠ 0` · goal -/
example (b : ℝ) (P : ℝ → Prop) (h : P b) : P (2 * b / 2) := by
  rw [mul_div_cancel_left₀ b two_ne_zero]
  exact h

/-! ## Endpoints and the final bound (theorem `linear_interp_error`) -/

/-! ### R25. `obtain ⟨h₁, h₂⟩ := hx` · context: `hx : x ∈ Set.Icc a b` → `h₁ : a ≤ x`, `h₂ : x ≤ b` -/
example (a b x : ℝ) (hx : x ∈ Set.Icc a b) (G : Prop) (k : a ≤ x → x ≤ b → G) : G := by
  obtain ⟨h₁, h₂⟩ := hx
  exact k h₁ h₂

/-! ### R26. `h.eq_or_lt` (`LE.le.eq_or_lt`) · `a ≤ b → a = b ∨ a < b` · context -/
example (a b : ℝ) (h : a ≤ b) (G : Prop) (k : a = b ∨ a < b → G) : G := by
  have h' := h.eq_or_lt
  exact k h'

/-! ### R27. `rcases h with rfl | h` · goal list: the `=` case with one variable substituted, and the `<` case -/
example (a b : ℝ) (P : ℝ → ℝ → Prop) (h : a = b ∨ a < b) (he : ∀ y, P y y) (hl : a < b → P a b) :
    P a b := by
  rcases h with rfl | h
  exact he a
  exact hl h

/-! ### R28. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · goal list: one goal per factor -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  apply mul_nonneg
  exact ha
  exact hb

/-! ### R29. `abs_mul` · `|a * b| = |a| * |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| * |b|)) : P |a * b| := by
  rw [abs_mul]
  exact h

/-! ### R30. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R31. `abs_two` · `|2| = 2` · goal -/
example (P : ℝ → Prop) (h : P 2) : P |2| := by
  rw [abs_two]
  exact h

/-! ### R32. `abs_neg` · `|-a| = |a|` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P |a|) : P |-a| := by
  rw [abs_neg]
  exact h

/-! ### R33. `abs_of_nonneg` · `0 ≤ a → |a| = a` · goal (here with `ha` given) -/
example (a : ℝ) (ha : 0 ≤ a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_nonneg ha]
  exact h

/-! ### R34. `gcongr` · goal `u / 2 * c ≤ v / 2 * c` → `u ≤ v` (side goal `0 ≤ c` taken from `hc`) -/
example (u v c : ℝ) (hc : 0 ≤ c) (h : u + 1 ≤ v) : u / 2 * c ≤ v / 2 * c := by
  gcongr
  linarith

/-! ### R35. `Set.Ioo_subset_Icc_self` · `Set.Ioo a b ⊆ Set.Icc a b`; applied to `hx : x ∈ Set.Ioo a b` -/
example (a b x : ℝ) (hx : x ∈ Set.Ioo a b) (G : Prop) (k : x ∈ Set.Icc a b → G) : G := by
  have hx' := Set.Ioo_subset_Icc_self hx
  exact k hx'

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Derivative of a scaled parabola: R1, R2, R5, R3, then R7 with `ring` -/
example (t : ℝ) : HasDerivAt (fun y => 3 * ((y - 1) * (y - 3))) (6 * t - 12) t := by
  have hid := hasDerivAt_id' t
  have hp := ((hid.sub_const 1).mul (hid.sub_const 3)).const_mul 3
  exact hp.congr_deriv (by ring)

/-! ### W2. Rolle on `[1, 3]` for `p y = (y - 1) * (y - 3)`: R11, R12, R17, R16 -/
example : ∃ c ∈ Set.Ioo (1 : ℝ) 3, 2 * c - 4 = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun y => (y - 1) * (y - 3)) (2 * t - 4) t := fun t =>
    (((hasDerivAt_id' t).sub_const 1).mul ((hasDerivAt_id' t).sub_const 3)).congr_deriv (by ring)
  have hc : Continuous (fun y : ℝ => (y - 1) * (y - 3)) :=
    continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  exact exists_hasDerivAt_eq_zero (by norm_num) hc.continuousOn (by norm_num) fun t _ => hd t

/-! ### W3. Choosing a constant to kill a value: R8, R13 -/
example (v p : ℝ) (hp : p ≠ 0) : v - v / p * p = 0 := by
  set K := v / p with hK
  rw [hK, div_mul_cancel₀ v hp]
  ring

/-! ### W4. Two Rolle points and their order: R19, R20, R21 -/
example (Q : ℝ → Prop) (h₁ : ∃ c ∈ Set.Ioo (0 : ℝ) 1, Q c) (h₂ : ∃ c ∈ Set.Ioo (1 : ℝ) 2, Q c) :
    ∃ c₁ c₂ : ℝ, c₁ < c₂ ∧ Q c₁ ∧ Q c₂ := by
  obtain ⟨c₁, hc₁, q₁⟩ := h₁
  obtain ⟨c₂, hc₂, q₂⟩ := h₂
  exact ⟨c₁, c₂, hc₁.2.trans hc₂.1, q₁, q₂⟩

end H067Guide
