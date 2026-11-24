/- Guide for M097 (Stationary distribution of a 2-state chain).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the swap chain, other vectors).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M097Guide

/-! # Part R · Reference entries -/

/-! ## Facts, `↔`, and taking hypotheses apart -/

/-! ### R1. `LT.lt.ne'` · `x < y → y ≠ x`; `have hne : y ≠ x := hxy.ne'` · context gains `hne`
`hxy.ne'` is dot notation: `hxy : x < y` has type `LT.lt x y`, so `hxy.ne'` means `LT.lt.ne' hxy`. -/
example {α : Type} [Preorder α] (x y : α) (hxy : x < y) (G : Prop) (h : y ≠ x → G) : G := by
  have hne : y ≠ x := hxy.ne'
  exact h hne

/-! ### R2. `constructor` on `↔` · goal `A ↔ B` → two goals `A → B` (case `mp`), `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exacts [hab, hba]

/-- A definition that unfolds to a conjunction, like a predicate packaging three conditions. -/
def Three (A B C : Prop) : Prop := A ∧ B ∧ C

/-! ### R3. `rintro ⟨-, hb, hc⟩` · goal `Three A B C → G` → goal `G`; context gains `hb`, `hc`
The pattern sees through the definition `Three` to `A ∧ B ∧ C`. `-` throws the first part away. -/
example (A B C G : Prop) (h : B → C → G) : Three A B C → G := by
  rintro ⟨-, hb, hc⟩
  exact h hb hc

/-! ### R4. `congrFun` · `f = g → ∀ x, f x = g x` · context gains one coordinate of a function equation
A vector `Fin 2 → ℝ` is a function, so `congrFun hfg 0` is "coordinate 0 of `hfg`". -/
example {α β : Type} (f g : α → β) (hfg : f = g) (x : α) (G : Prop) (h : f x = g x → G) : G := by
  have hx := congrFun hfg x
  exact h hx

/-! ## Evaluating a row vector times a matrix -/

/-- A named matrix, to show how `simp [D]` unfolds a definition. -/
def D : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]

/-! ### R5. `simp [D] at hx` · context: hypothesis `hx` simplified in place (definition `D` unfolded) -/
example (x : ℝ) (hx : D 1 0 = x) (h : (3 : ℝ) = x → x = 3) : x = 3 := by
  simp [D] at hx
  exact h hx

/-! ### R6. `Matrix.vecMul`, `dotProduct` · goal: `Matrix.vecMul v M j` (row vector `v` times `M`,
coordinate `j`) → `v ⬝ᵥ (column j)` → `∑ x, v x * M x j` -/
example (v : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) (P : ℝ → Prop)
    (h : P (∑ i, v i * M i j)) : P (Matrix.vecMul v M j) := by
  simp only [Matrix.vecMul]
  simp only [dotProduct]
  exact h

/-! ### R7. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R8. Entry of a matrix literal `!![a, b; c, d] i j` · goal (`simp` reads the entry) -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (!![a, b; c, d] 1 0) := by
  simp
  exact h

/-! ## Vector equations → coordinates -/

/-! ### R9. `ext i` (lemma `funext`) · goal `v = w` → context gains `i`, goal is one coordinate -/
example (v w : Fin 2 → ℝ) (h : ∀ i, v i = w i) : v = w := by
  ext i
  exact h i

/-! ### R10. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exacts [h0, h1]

/-! ### R11. Entry of a vector literal `![x, y] k` · goal (`simp` reads the entry) -/
example {α : Type} (x y : α) (P : α → Prop) (h : P y) : P (![x, y] 1) := by
  simp
  exact h

/-! ## Closing scalar goals -/

/-! ### R12. `field_simp` · goal: denominators cleared (needs `y ≠ 0` or `0 < y` in the context) -/
example {α : Type} [Field α] (x y z : α) (hy : y ≠ 0) (h : x = y * z) : x / y = z := by
  field_simp
  exact h

/-! ### R13. `nlinarith` · closes `=`, `≤`, `<` goals that follow from products of two hypotheses
Here it multiplies `hc : 0 ≤ c` by `hs : x + y = 1`; `linarith` alone fails. -/
example (x y c : ℝ) (hc : 0 ≤ c) (hs : x + y = 1) : c * x + c * y = c := by nlinarith

/-! ### R14. `rintro rfl` · goal `y = e → P y` → `P e`; the variable `y` is replaced everywhere -/
example {α : Type} (f : α → α) (x : α) (P : α → Prop) (h : P (f x)) (y : α) :
    y = f x → P y := by
  rintro rfl
  exact h

/-! ### R15. `refine ⟨?_, ?_, ?_⟩` on a definition · goal `Three A B C` → goals `A`, `B`, `C`
The anonymous constructor sees through `Three` to `A ∧ B ∧ C`. -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : Three A B C := by
  refine ⟨?_, ?_, ?_⟩
  exacts [ha, hb, hc]

/-! ### R16. `positivity` · closes `0 ≤ e` / `0 < e` built from `+ * /` and hypotheses on atoms -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : 0 ≤ x / y := by positivity

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A vector equation by coordinates: R9, R10, then `simp` reads each side (R11) -/
example (v : Fin 2 → ℝ) (h0 : v 0 = 5) (h1 : v 1 = 7) : v = ![5, 7] := by
  ext i
  fin_cases i
  · simp
    exact h0
  · simp
    exact h1

/-- The swap chain: from either state, move to the other one. -/
def Sw : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-! ### W2. One coordinate of `v · Sw = v`, evaluated in the context: R4, then R5 with R6–R8 -/
example (v : Fin 2 → ℝ) (hfix : Matrix.vecMul v Sw = v) : v 1 = v 0 := by
  have h0 := congrFun hfix 0
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Sw] at h0
  exact h0

/-! ### W3. Clear a denominator, then finish with the hypotheses: R12, then `linarith` -/
example (x y : ℝ) (h1 : x + y = 1) (h2 : x = 2 * y) : x = 2 / 3 := by
  field_simp
  linarith

/-! ### W4. Checking a candidate vector: R14, R11, R12, then `ring` -/
example (s t : ℝ) (hst : s + t ≠ 0) (v : Fin 2 → ℝ) :
    v = ![(s - t) / (s + t), 2 * t / (s + t)] → v 0 + v 1 = 1 := by
  rintro rfl
  simp
  field_simp
  ring

end M097Guide
