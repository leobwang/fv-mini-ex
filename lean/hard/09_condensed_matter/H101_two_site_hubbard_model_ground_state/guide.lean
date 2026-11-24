/- Guide for H101 (Two-site Hubbard model ground state).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a 2×2 matrix, `√5`, `√(a² + 1)`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix

namespace H101Guide

/-! # Part R · Reference entries -/

/-! ## Square roots and the quadratic identity (`E0_quad`) -/

/-! ### R1. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · context gains `h : √x ^ 2 = x` -/
example (x : ℝ) (hx : 0 ≤ x) (G : Prop) (g : G) : G := by
  have h := Real.sq_sqrt hx
  exact g

/-! ### R2. `positivity` · closes a goal `0 ≤ e` or `0 < e` built from squares, sums, products -/
example (a b : ℝ) : 0 ≤ a ^ 2 + 16 * b ^ 2 := by
  positivity

/-! ### R3. `unfold D` · goal: the defined name `D` → its body -/
noncomputable def F (a b : ℝ) : ℝ := (a - b) / 3
example (a b : ℝ) (P : ℝ → Prop) (h : P ((a - b) / 3)) : P (F a b) := by
  unfold F
  exact h

/-! ### R4. `linear_combination e` · closes `L = R` when `L - R = c · (lhs - rhs of h)` is a ring identity
`e` is a combination of hypotheses with ring coefficients: `h`, `h / 4`, `d ^ 2 * h`, `2 * h₁ + h₂`. -/
example (x y : ℝ) (h : x ^ 2 = y) : (x / 2) ^ 2 = y / 4 := by
  linear_combination h / 4

/-! ## Strict bounds via `|U|` (`E0_lt`) -/

/-! ### R5. `Real.sqrt_sq_eq_abs` · `√(x ^ 2) = |x|`; `rw [← Real.sqrt_sq_eq_abs]` turns `|x|` into a root -/
example (x : ℝ) (P : ℝ → Prop) (h : P (√(x ^ 2))) : P |x| := by
  rw [← Real.sqrt_sq_eq_abs]
  exact h

/-! ### R6. `Real.sqrt_lt_sqrt` · `0 ≤ x → x < y → √x < √y` · goal → two goals -/
example (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : √x < √y := by
  apply Real.sqrt_lt_sqrt
  exact hx
  exact hxy

/-! ### R7. `sq_nonneg` · `0 ≤ a ^ 2` · context gains the fact -/
example (a : ℝ) (G : Prop) (g : G) : G := by
  have h := sq_nonneg a
  exact g

/-! ### R8. `abs_pos` · `0 < |a| ↔ a ≠ 0`; `abs_pos.mpr ha : 0 < |a|` · context gains the fact -/
example (a : ℝ) (ha : a ≠ 0) (G : Prop) (g : G) : G := by
  have h := abs_pos.mpr ha
  exact g

/-! ### R9. `pow_pos` · `0 < a → ∀ n, 0 < a ^ n` · context gains the fact -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (g : G) : G := by
  have h := pow_pos ha 2
  exact g

/-! ### R10. `simp at h` · context: `h` simplified in place (`|a| ^ 2` → `a ^ 2` by `sq_abs`) -/
example (a : ℝ) (h : 0 < |a| ^ 2) (G : Prop) (g : 0 < a ^ 2 → G) : G := by
  simp at h
  exact g h

/-! ### R11. `linarith` · closes a linear (in)equality that follows from the hypotheses
Nonlinear pieces such as `t ^ 2`, `√e`, `E0 t U` count as opaque atoms. -/
example (x y : ℝ) (hy : 0 < y) : x < x + 16 * y := by
  linarith

/-! ### R12. `cases abs_cases a` · goal list: one goal per sign of `a`, each with a fact about `|a|`
`linarith` reads both halves of the `∧` fact `h✝` (an unnamed hypothesis). -/
example (a b : ℝ) (h : |a| < b) : a < b ∧ -a < b := by
  cases abs_cases a
  all_goals constructor <;> linarith

/-! ## Positivity after scaling (`block_nonneg`) -/

/-! ### R13. `mul_nonneg_iff_of_pos_left` · `0 < c → (0 ≤ c * b ↔ 0 ≤ b)`
`rw [← mul_nonneg_iff_of_pos_left hc]` turns the goal `0 ≤ b` into `0 ≤ c * b`. -/
example (b c : ℝ) (hc : 0 < c) (h : 0 ≤ c * b) : 0 ≤ b := by
  rw [← mul_nonneg_iff_of_pos_left hc]
  exact h

/-! ## Splitting the main statement (`ground_state_energy`) -/

/-! ### R14. `obtain ⟨h₁, h₂⟩ := e` · context: a fact `A ∧ B` → two facts -/
example (A B G : Prop) (e : A ∧ B) (g : A → B → G) : G := by
  obtain ⟨h₁, h₂⟩ := e
  exact g h₁ h₂

/-! ### R15. `refine ⟨⟨v, ?_, ?_⟩, fun x => ?_⟩` · goal list: `(∃ v, A v ∧ B v) ∧ ∀ x, C x` → three goals
`v` is your witness; each `?_` becomes a goal, and `fun x => ?_` puts `x` in its goal's context. -/
example {α β : Type} (A B : α → Prop) (C : β → Prop) (v : α) (ha : A v) (hb : B v) (hc : ∀ x, C x) :
    (∃ w, A w ∧ B w) ∧ ∀ x, C x := by
  refine ⟨⟨v, ?_, ?_⟩, fun x => ?_⟩
  exact ha
  exact hb
  exact hc x

/-! ## A vector is nonzero -/

/-! ### R16. `intro h` on `≠` · goal `a ≠ b` (that is, `a = b → False`) → `h : a = b ⊢ False` -/
example {α : Type} (a b : α) (k : a = b → False) : a ≠ b := by
  intro h
  exact k h

/-! ### R17. `congrFun h i` · `f = g → f i = g i` · context gains one component of a vector equation -/
example {α : Type} (v w : Fin 4 → α) (h : v = w) (G : Prop) (g : G) : G := by
  have h₂ := congrFun h 2
  exact g

/-! ### R18. `simp at h` on a vector literal · context: `![a, b, 2 * c, d] 2 = 0 2` → `c = 0`
`simp` reads entry 2 of the literal, `0 2` is `0`, and `2 * c = 0` becomes `c = 0`. -/
example (a b c d : ℝ) (h : ![a, b, 2 * c, d] 2 = (0 : Fin 4 → ℝ) 2) (G : Prop) (g : c = 0 → G) : G := by
  simp at h
  exact g h

/-! ### R19. `exact hne heq` · closes `False` from `hne : a ≠ b` and `heq : a = b` -/
example {α : Type} (a b : α) (hne : a ≠ b) (heq : a = b) : False := by
  exact hne heq

/-! ## Vector equations and quadratic forms, entry by entry -/

/-! ### R20. `ext i` on vectors (lemma `funext`) · goal `v = w` → `i : Fin 4 ⊢ v i = w i` -/
example {α : Type} (v w : Fin 4 → α) (h : ∀ i, v i = w i) : v = w := by
  ext i
  exact h i

/-! ### R21. `Matrix.mulVec` · goal: `(M *ᵥ v) i` → row `i` of `M` dotted with `v` -/
example {α : Type} [NonUnitalNonAssocSemiring α] (M : Matrix (Fin 4) (Fin 4) α) (v : Fin 4 → α)
    (i : Fin 4) (P : α → Prop) (h : P ((fun j => M i j) ⬝ᵥ v)) : P ((M *ᵥ v) i) := by
  simp only [mulVec]
  exact h

/-! ### R22. `dotProduct` · goal: `v ⬝ᵥ w` → `∑ i, v i * w i` -/
example {α : Type} [Mul α] [AddCommMonoid α] (v w : Fin 4 → α) (P : α → Prop)
    (h : P (∑ i, v i * w i)) : P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R23. `Fin.sum_univ_four` · goal: a sum over `Fin 4` → four terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 4 → β) (P : β → Prop) (h : P (f 0 + f 1 + f 2 + f 3)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_four]
  exact h

/-! ### R24. `Pi.smul_apply`, `smul_eq_mul` · goal: entry of `c • v` → `c * v i` -/
example (c : ℝ) (v : Fin 4 → ℝ) (i : Fin 4) (P : ℝ → Prop) (h : P (c * v i)) : P ((c • v) i) := by
  rw [Pi.smul_apply]
  rw [smul_eq_mul]
  exact h

/-! ### R25. `first | ring1 | linear_combination h` · closes each goal with the first tactic that works
`ring1` is `ring` that fails (instead of leaving a normalised goal) when the identity is false. -/
example (a b : ℝ) (h : a ^ 2 = b) : a + a = 2 * a ∧ a * a = b := by
  constructor
  all_goals first | ring1 | linear_combination h

/-! ## Nonnegative products for `nlinarith` -/

/-! ### R26. `nlinarith [p₁, p₂]` · closes a polynomial inequality
It adds the facts `pᵢ`, multiplies pairs of hypotheses, then runs `linarith`. Give it the squares. -/
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ### R27. `mul_nonneg` · `0 ≤ a → 0 ≤ b → 0 ≤ a * b` · context gains the fact -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (G : Prop) (g : G) : G := by
  have h := mul_nonneg ha hb
  exact g

/-! ### R28. `sub_nonneg` · `0 ≤ a - b ↔ b ≤ a`; `sub_nonneg.mpr hba : 0 ≤ a - b` · context gains the fact -/
example (a b : ℝ) (hba : b ≤ a) (G : Prop) (g : G) : G := by
  have h := sub_nonneg.mpr hba
  exact g

/-! ### R29. `neg_nonneg` · `0 ≤ -a ↔ a ≤ 0`; `neg_nonneg.mpr ha : 0 ≤ -a` · context gains the fact -/
example (a : ℝ) (ha : a ≤ 0) (G : Prop) (g : G) : G := by
  have h := neg_nonneg.mpr ha
  exact g

/-! ### R30. `h.le` (lemma `LT.lt.le`) · `a < b → a ≤ b` · context gains the weak inequality -/
example (a b : ℝ) (hlt : a < b) (G : Prop) (g : G) : G := by
  have h := hlt.le
  exact g

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A root of a quadratic with `√`: R1, R2, R3, R4 on `r = (1 - √5) / 2`, `r² - r - 1 = 0` -/
noncomputable def r : ℝ := (1 - Real.sqrt 5) / 2
example : r ^ 2 - r - 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)
  unfold r
  linear_combination h / 4

/-! ### W2. A strict bound through `|a|`: R5, R6, R7, R11, R12 -/
example (a : ℝ) : a - √(a ^ 2 + 1) < 0 := by
  have hlt : |a| < √(a ^ 2 + 1) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  cases abs_cases a <;> linarith

/-! ### W3. Nonnegativity by scaling to a square: R13, then `rw [key]`, then R2 -/
example (s d : ℝ) : 0 ≤ 2 * s ^ 2 + 2 * s * d + d ^ 2 / 2 := by
  have key : 2 * (2 * s ^ 2 + 2 * s * d + d ^ 2 / 2) = (2 * s + d) ^ 2 := by ring
  rw [← mul_nonneg_iff_of_pos_left (show (0 : ℝ) < 2 by norm_num), key]
  positivity

/-! ### W4. An eigenvector of a 2×2 matrix: R20, `fin_cases`, R21–R24 (`Fin.sum_univ_two` for `Fin 2`) -/
example : !![(2 : ℝ), 1; 1, 2] *ᵥ ![1, 1] = (3 : ℝ) • ![1, 1] := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  all_goals norm_num

/-! ### W5. A variational bound for the same matrix (lowest eigenvalue 1): unfold, then R26 -/
example (x : Fin 2 → ℝ) : 1 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (!![(2 : ℝ), 1; 1, 2] *ᵥ x) := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 + x 1)]

end H101Guide
