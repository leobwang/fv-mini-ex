/- Guide for M172 (Superexchange from the Hubbard dimer spectrum).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other matrices, other
inequalities).
Assumed: Lean basics.
-/
import Mathlib

open Matrix

namespace M172Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · A vector equation → four number equations -/

/-! ### R1. `ext i` (lemma `funext`) · goal `v = w` (vectors) → context gains `i`, goal is one component
A vector `Fin 4 → ℝ` is a function, so two vectors are equal when every component is. -/
example (v w : Fin 4 → ℝ) (h : ∀ i, v i = w i) : v = w := by
  ext i
  exact h i

/-! ### R2. `fin_cases i` on `i : Fin 4` · context loses `i`; goal → four goals, one per index
`(fun i => i) ⟨2, ⋯⟩` is how Lean prints the index `2`. -/
example (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (i : Fin 4) : P i := by
  fin_cases i
  exacts [h0, h1, h2, h3]

/-! ### R3. `Matrix.mulVec` · goal: component `i` of `M *ᵥ v` → row `i` of `M` dotted with `v` -/
example (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (i : Fin 4) (P : ℝ → Prop)
    (h : P ((fun j => M i j) ⬝ᵥ v)) : P ((M *ᵥ v) i) := by
  simp only [Matrix.mulVec]
  exact h

/-! ### R4. `dotProduct` · goal: `u ⬝ᵥ v` → the sum `∑ i, u i * v i` -/
example (u v : Fin 4 → ℝ) (P : ℝ → Prop) (h : P (∑ i, u i * v i)) : P (u ⬝ᵥ v) := by
  simp only [dotProduct]
  exact h

/-! ### R5. `Fin.sum_univ_four` · goal: a sum over `Fin 4` → four terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 4 → β) (P : β → Prop) (h : P (f 0 + f 1 + f 2 + f 3)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_four]
  exact h

/-! ### R6. Component of a literal vector `![a, b, c, d] i` (`Matrix.cons_val_…`) · goal
`simp` applies these by itself. -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (![a, b, c, d] 2) := by
  simp
  exact h

/-! ### R7. Entry of a literal matrix `!![…] i j` (`Matrix.of_apply`, `Matrix.cons_val_…`) · goal
`simp` applies these by itself; it works the same for 4×4 literals. -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (!![a, b; c, d] 1 0) := by
  simp
  exact h

/-! ### R8. `Pi.zero_apply` · goal: component of the zero vector → `0` -/
example (i : Fin 4) (P : ℝ → Prop) (h : P 0) : P ((0 : Fin 4 → ℝ) i) := by
  rw [Pi.zero_apply]
  exact h

/-! ## Part 2 · From an eigenvalue equation to a polynomial in `E` -/

/-! ### R9. `obtain ⟨x, hx1, hx2⟩ := h` · context: `h : ∃ x, A x ∧ B x` → `x`, `hx1 : A x`, `hx2 : B x` -/
example {α : Type} (A B : α → Prop) (G : Prop) (h : ∃ x, A x ∧ B x) (g : ∀ x, A x → B x → G) : G := by
  obtain ⟨x, hx1, hx2⟩ := h
  exact g x hx1 hx2

/-! ### R10. `congrFun h i` · from `h : f = g` (functions) to `f i = g i`; `have h0 := …` puts it in the context -/
example (f g : Fin 4 → ℝ) (hfg : f = g) (G : Prop) (k : f 0 = g 0 → G) : G := by
  have h0 := congrFun hfg 0
  exact k h0

/-! ### R11. `Pi.smul_apply`, `smul_eq_mul` · goal: component of `c • v` → `c * v i` -/
example (c : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) (P : ℝ → Prop) (h : P (c * v i)) : P ((c • v) i) := by
  rw [Pi.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R12. `simp [names] at h` · context: rewrites the hypothesis `h`, not the goal
`simp … at h0 h1` works on several hypotheses at once. -/
example (u v : Fin 4 → ℝ) (c : ℝ) (G : Prop) (h : u ⬝ᵥ v = (c • u) 0)
    (k : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = c * u 0 → G) : G := by
  simp [dotProduct, Fin.sum_univ_four] at h
  exact k h

/-! ### R13. `by_contra hne` · goal `G` → context gains `hne : ¬G`, goal `False` -/
example (G : Prop) (k : ¬G → False) : G := by
  by_contra hne
  exact k hne

/-! ### R14. `apply hv0` with `hv0 : v ≠ 0` · goal `False` → goal `v = 0`
`v ≠ 0` unfolds to `v = 0 → False`, so applying it to `False` leaves `v = 0` to prove. -/
example (v : Fin 4 → ℝ) (hv0 : v ≠ 0) (h : v = 0) : False := by
  apply hv0
  exact h

/-! ### R15. `linear_combination c₁ * h₁ + c₂ * h₂` · closes `lhs = rhs` when `lhs - rhs` equals
`c₁ * (h₁.lhs - h₁.rhs) + c₂ * (h₂.lhs - h₂.rhs)` as polynomials (checked by `ring`).
The coefficients `cᵢ` may be any expressions, variables included. -/
example (x y a b c : ℝ) (h1 : x + y = a) (h2 : x - y = b) : c * (2 * x) = c * (a + b) := by
  linear_combination c * h1 + c * h2

/-! ### R16. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp` takes the left-to-right direction -/
example (a b : ℝ) (hab : a * b = 0) (G : Prop) (k : a = 0 ∨ b = 0 → G) : G := by
  have h := mul_eq_zero.mp hab
  exact k h

/-! ### R17. `Or.resolve_left` · `A ∨ B → ¬A → B`: rule out the left case -/
example (A B : Prop) (hab : A ∨ B) (hna : ¬A) : B := by
  exact hab.resolve_left hna

/-! ### R18. `LT.lt.ne` · `a < b → a ≠ b`; written `hE.ne` for `hE : E < 0`, giving `E ≠ 0` -/
example (x : ℝ) (hx : x < 0) (G : Prop) (k : x ≠ 0 → G) : G := by
  have h := hx.ne
  exact k h

/-! ### R19. `Eq.symm`, `Eq.trans` · `h.symm.trans h'` chains `h : a = b` and `h' : a = c` into `b = c` -/
example (a b c : ℝ) (h : a = b) (h' : a = c) (G : Prop) (k : b = c → G) : G := by
  have hbc := h.symm.trans h'
  exact k hbc

/-! ### R20. `linarith` · closes a linear (in)equality that follows from linear hypotheses -/
example (x y : ℝ) (h1 : x - y = 0) (h2 : y = 0) : x = 0 := by
  linarith

/-! ## Part 3 · Inequalities with a positive denominator -/

/-! ### R21. `le_div_iff₀` · `0 < c → (a ≤ b / c ↔ a * c ≤ b)` · goal: clear the denominator on the right -/
example (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  rw [le_div_iff₀ hc]
  exact h

/-! ### R22. `nlinarith` · closes a polynomial (in)equality; it also multiplies pairs of hypotheses
Extra facts go in brackets: `nlinarith [sq_nonneg (x - y), h]`. -/
example (x y c : ℝ) (hx : 0 < x) (h : x * (y + x) = c) : x * y ≤ c := by
  nlinarith

/-! ### R23. `field_simp` · goal: clears every denominator it knows is nonzero (multiplies out)
It finds `c ≠ 0` from a hypothesis `hc : 0 < c` or `hc : c ≠ 0` in the context. It may close the
goal itself; when it leaves a polynomial identity, finish with `ring`. -/
example (a c : ℝ) (hc : 0 < c) : 3 * a / c = (a + 2 * a) / c := by
  field_simp
  ring

/-! ### R24. `div_le_iff₀` · `0 < c → (b / c ≤ a ↔ b ≤ a * c)` · goal: clear the denominator on the left -/
example (a b c : ℝ) (hc : 0 < c) (h : b ≤ a * c) : b / c ≤ a := by
  rw [div_le_iff₀ hc]
  exact h

/-! ### R25. `pow_le_pow_left₀` · `0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n` -/
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (G : Prop) (k : a ^ 2 ≤ b ^ 2 → G) : G := by
  have h := pow_le_pow_left₀ ha hab 2
  exact k h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A matrix times a literal vector, all components at once: R1, R2, R3–R8 -/
def K (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0, a, 0, 0; a, 0, 0, 0; 0, 0, 0, a; 0, 0, a, 0]
example (a : ℝ) : K a *ᵥ ![1, -1, 0, 0] = ![-a, a, 0, 0] := by
  ext i
  fin_cases i
  all_goals simp [K, mulVec, dotProduct, Fin.sum_univ_four]

/-! ### W2. Component equations of an eigenvalue equation, then one combination: R9–R12, R15
For `M = [[0, a], [a, 0]]` and `M v = E v`, the two equations combine to `(E² - a²) · v 0 = 0`. -/
def M2 (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, a; a, 0]
example (a E : ℝ) (hv : ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M2 a *ᵥ v = E • v) :
    ∃ v : Fin 2 → ℝ, (E ^ 2 - a ^ 2) * v 0 = 0 := by
  obtain ⟨v, _, hv⟩ := hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [M2, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  exact ⟨v, by linear_combination (-E) * h0 + (-a) * h1⟩

/-! ### W3. A product that vanishes with a nonzero factor: R16, R17, R18 -/
example (x y : ℝ) (hx : x < 0) (h : x * y = 0) : y = 0 := by
  exact (mul_eq_zero.mp h).resolve_left hx.ne

/-! ### W4. Rewrite a side as one fraction, then clear it: R23 (inside a `have`), R24, R20 -/
example (a b c : ℝ) (hc : 0 < c) (hb : 0 ≤ b) (ha : a ≤ c) : a / c - b / c ≤ 1 := by
  have h : a / c - b / c = (a - b) / c := by
    field_simp
  rw [h, div_le_iff₀ hc]
  linarith

end M172Guide
