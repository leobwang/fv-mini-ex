/- Guide for M162 (Fermi–Dirac occupation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: Lean basics. `rexp` is how the infoview prints `Real.exp`.
-/
import Mathlib

open Real Filter Topology

namespace M162Guide

/-! # Part R · Reference entries -/

/-! ## Bounds: positivity and a quotient below 1 -/

/-! ### R1. `unfold g` · goal: the defined name `g` → its body -/
def g (a t : ℝ) : ℝ := a * t + 1
example (a t : ℝ) (P : ℝ → Prop) (h : P (a * t + 1)) : P (g a t) := by
  unfold g
  exact h

/-! ### R2. `have := Real.exp_pos x` · context gains `this : 0 < rexp x`
`Real.exp_pos : ∀ x : ℝ, 0 < rexp x`. A `have` with no name calls the new fact `this`. -/
example (x : ℝ) (G : Prop) (h : 0 < rexp x → G) : G := by
  have := Real.exp_pos x
  exact h this

/-! ### R3. `positivity` · closes a goal `0 < e` / `0 ≤ e` / `e ≠ 0` by the shape of `e`
It knows `rexp _ > 0`, `1 > 0`, and that `+`, `*`, `/` of positives are positive. -/
example (x : ℝ) : 0 < 1 / (rexp x + 1) := by
  positivity

/-! ### R4. `div_lt_one` · `0 < b → (a / b < 1 ↔ a < b)` · goal `a / b < 1` → `a < b`
Write `rw [div_lt_one (by positivity)]` to prove `0 < b` on the spot. -/
example (a b : ℝ) (hb : 0 < b) (h : a < b) : a / b < 1 := by
  rw [div_lt_one hb]
  exact h

/-! ### R5. `linarith` · closes a linear (in)equality from the context; `rexp x` counts as an unknown -/
example (x : ℝ) (hx : 0 < rexp x) : 1 < rexp x + 1 := by
  linarith

/-! ## Symmetry: `exp (-y) = (exp y)⁻¹` and clearing denominators -/

/-! ### R6. `Real.exp_neg` · `rexp (-x) = (rexp x)⁻¹`; right to left: `rw [← Real.exp_neg]` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (rexp (-x))) : P (rexp x)⁻¹ := by
  rw [← Real.exp_neg]
  exact h

/-! ### R7. `ring_nf` · normalizes ring expressions everywhere, also inside `rexp (…)`; closes the
goal when both sides become the same text -/
example (a b c : ℝ) : rexp (c * (a - b)) = rexp (-(c * (b - a))) := by
  ring_nf

/-! ### R8. `field_simp` · goal: clears every denominator it can prove nonzero (from `0 < a`,
`a ≠ 0` in the context, or by `positivity`), leaving an equation without `/` and `⁻¹` -/
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (h : b + a = a * b * c) : 1 / a + 1 / b = c := by
  field_simp
  exact h

/-! ### R9. `ring` · closes an identity of commutative rings; `rexp x` counts as an unknown -/
example (x : ℝ) : (rexp x + 1) * (1 + rexp x) = 1 + rexp x + rexp x * (rexp x + 1) := by
  ring

/-! ## Monotonicity -/

/-! ### R10. `intro a b hab` on `Antitone f` · context gains `a b` and `hab : a ≤ b`; goal `f b ≤ f a`
`Antitone f` is defined as `∀ ⦃a b⦄, a ≤ b → f b ≤ f a`, so `intro` sees through it. -/
example (f : ℝ → ℝ) (h : ∀ a b, a ≤ b → f b ≤ f a) : Antitone f := by
  intro a b hab
  exact h a b hab

/-! ### R11. `gcongr` · goal `lhs ≤ rhs` with the same shape on both sides → `≤` between the parts
that differ. It knows `1 / _` is decreasing on positives, `rexp` and `_ + 1` are increasing.
It closes the new goals from context hypotheses when it can; here it cannot, so `x ≤ y` remains. -/
example (x y : ℝ) (h : y - x ≥ 0) : 1 / (rexp y + 1) ≤ 1 / (rexp x + 1) := by
  gcongr
  linarith

/-! ### R12. `gcongr` side goal · `c * x ≤ c * y` needs `0 ≤ c`. With `hc : 0 ≤ c` in the context
`gcongr` uses it silently; here only `0 ≤ c - 1` is known, so `0 ≤ c` is left as a goal -/
example (c x y : ℝ) (h : x ≤ y) (hc : 0 ≤ c - 1) : rexp (c * x) ≤ rexp (c * y) := by
  gcongr
  linarith

/-! ## Limits: `Tendsto` building blocks -/

/-! ### R13. `tendsto_id` · `Tendsto id l l`: the identity `t ↦ t` tends to `∞` as `t → ∞` -/
example : Tendsto (fun t : ℝ => t) atTop atTop := by
  exact tendsto_id

/-! ### R14. `tendsto_const_nhds` · `Tendsto (fun _ => c) l (𝓝 c)` · context gains it
`(x := c)` fills the implicit argument named `x` (the constant), so Lean knows which `c`. -/
example {α : Type} (l : Filter α) (c : ℝ) (G : Prop) (k : Tendsto (fun _ : α => c) l (𝓝 c) → G) :
    G := by
  have h := tendsto_const_nhds (x := c) (f := l)
  exact k h

/-! ### R15. `Filter.Tendsto.atTop_mul_neg` · `C < 0 → f → ∞ → g → C → f * g → -∞` · context
Dot notation: `hf.atTop_mul_neg hC hk` is `Filter.Tendsto.atTop_mul_neg hC hf hk`. -/
example {α : Type} {l : Filter α} (f k : α → ℝ) (C : ℝ) (hC : C < 0) (hf : Tendsto f l atTop)
    (hk : Tendsto k l (𝓝 C)) (G : Prop) (e : Tendsto (fun x => f x * k x) l atBot → G) : G := by
  have h := hf.atTop_mul_neg hC hk
  exact e h

/-! ### R16. `Real.tendsto_exp_atBot` · `Tendsto rexp atBot (𝓝 0)`: `exp t → 0` as `t → -∞` -/
example (G : Prop) (e : Tendsto rexp atBot (𝓝 0) → G) : G := by
  have h := Real.tendsto_exp_atBot
  exact e h

/-! ### R17. `Filter.Tendsto.comp` · `Tendsto k y z → Tendsto f x y → Tendsto (k ∘ f) x z` · context -/
example {α β γ : Type} (f : α → β) (k : β → γ) (x : Filter α) (y : Filter β) (z : Filter γ)
    (hk : Tendsto k y z) (hf : Tendsto f x y) (G : Prop) (e : Tendsto (k ∘ f) x z → G) : G := by
  have h := hk.comp hf
  exact e h

/-! ### R18. `Filter.Tendsto.add_const` · `f → a` gives `f + b → a + b` · context -/
example {α : Type} {l : Filter α} (f : α → ℝ) (a b : ℝ) (hf : Tendsto f l (𝓝 a)) (G : Prop)
    (e : Tendsto (fun x => f x + b) l (𝓝 (a + b)) → G) : G := by
  have h := hf.add_const b
  exact e h

/-! ### R19. `Filter.Tendsto.div` · `f → a`, `k → b`, `b ≠ 0` give `f / k → a / b` · context
`f / k` between functions is the pointwise quotient `fun x => f x / k x`. -/
example {α : Type} {l : Filter α} (f k : α → ℝ) (a b : ℝ) (hf : Tendsto f l (𝓝 a))
    (hk : Tendsto k l (𝓝 b)) (hb : b ≠ 0) (G : Prop) (e : Tendsto (f / k) l (𝓝 (a / b)) → G) :
    G := by
  have h := hf.div hk hb
  exact e h

/-! ### R20. `simp only [Function.comp_def] at h` · context: `(k ∘ f) x` → `k (f x)` inside `h`
`Function.comp_def : k ∘ f = fun x => k (f x)`. -/
example (f k : ℝ → ℝ) (P : (ℝ → ℝ) → Prop) (h : P (fun x => (k ∘ f) x + 1)) :
    P (fun x => k (f x) + 1) := by
  simp only [Function.comp_def] at h
  exact h

/-! ### R21. `simp only [zero_add, div_one] at h` · context: `0 + a` → `a`, `a / 1` → `a` inside `h` -/
example (a : ℝ) (P : ℝ → Prop) (h : P (a / (0 + 1))) : P a := by
  simp only [zero_add, div_one] at h
  exact h

/-! ### R22. `exact h` up to unfolding · closes the goal when `h`'s type is the goal once
definitions are unfolded (here `g a t` unfolds to `a * t + 1`); no `unfold` needed -/
example (a t : ℝ) (P : ℝ → Prop) (h : P (a * t + 1)) : P (g a t) := by
  exact h

/-! # Part W · Worked combinations (not the exercise's functions) -/

/-! ### W1. A quotient below 1: R2, R4 (side goal by R3), R5 -/
example (t : ℝ) : rexp t / (rexp t + 1) < 1 := by
  have := Real.exp_pos t
  rw [div_lt_one (by positivity)]
  linarith

/-! ### W2. `exp (-t) · exp t = 1`: R6 left to right, then R8 closes it -/
example (t : ℝ) : rexp (-t) * rexp t = 1 := by
  rw [Real.exp_neg]
  field_simp

/-! ### W3. Antitone with a parameter: R10, R1, R11 (and R12's side goal from `hc`) -/
noncomputable def q (c t : ℝ) : ℝ := rexp (-(c * t))
example (c : ℝ) (hc : 0 ≤ c) : Antitone (q c) := by
  intro a b hab
  unfold q
  gcongr

/-! ### W4. A limit chain: R13 + R14 into R15, then R16, R17, R18, R20, R21 -/
example : Tendsto (fun t : ℝ => rexp (t * (-3)) + 2) atTop (𝓝 2) := by
  have h1 : Tendsto (fun t : ℝ => t * (-3)) atTop atBot :=
    tendsto_id.atTop_mul_neg (by norm_num) tendsto_const_nhds
  have h2 := (Real.tendsto_exp_atBot.comp h1).add_const 2
  simp only [Function.comp_def, zero_add] at h2
  exact h2

end M162Guide
