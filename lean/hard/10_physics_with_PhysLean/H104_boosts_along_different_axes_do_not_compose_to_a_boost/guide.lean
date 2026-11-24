/- Guide for H104 (Boosts along different axes do not compose to a boost).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (one boost, a boost squared, reals).
Assumed: Lean basics.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Basic

open LorentzGroup Matrix

namespace H104Guide

/-! # Part R · Reference entries -/

/-! ## The Lorentz factor is nonzero -/

/-! ### R1. `rw [abs_lt] at h` · `|a| < b ↔ -b < a ∧ a < b` · context: `h` is rewritten -/
example (a b : ℝ) (h : |a| < b) (P : Prop) (k : -b < a ∧ a < b → P) : P := by
  rw [abs_lt] at h
  exact k h

/-! ### R2. `nlinarith` · closes a polynomial inequality over `ℝ`
It splits `∧` hypotheses and multiplies pairs of hypotheses before running linear arithmetic. -/
example (a : ℝ) (h : -2 < a ∧ a < 2) : 0 < 4 - a ^ 2 := by
  nlinarith

/-! ### R3. `unfold γ` · goal: `γ β` → its definition `1 / √(1 - β ^ 2)` -/
example (β : ℝ) (P : ℝ → Prop) (h : P (1 / √(1 - β ^ 2))) : P (γ β) := by
  unfold γ
  exact h

/-! ### R4. `apply one_div_ne_zero` · `a ≠ 0 → 1 / a ≠ 0` · goal: `1 / a ≠ 0` → `a ≠ 0` -/
example (a : ℝ) (h : a ≠ 0) : 1 / a ≠ 0 := by
  apply one_div_ne_zero
  exact h

/-! ### R5. `rw [Real.sqrt_ne_zero']` · `√x ≠ 0 ↔ 0 < x` · goal -/
example (x : ℝ) (h : 0 < x) : √x ≠ 0 := by
  rw [Real.sqrt_ne_zero']
  exact h

/-! ## An entry of a product of Lorentz transformations -/

/-! ### R6. `lorentzGroupIsGroup_mul_coe` · `↑(A * B) = ↑A * ↑B` · goal: matrix of a product
`↑A` (written `A.1`) is the matrix of `A : LorentzGroup d`. -/
example {d : ℕ} (A B : LorentzGroup d) (r c : Fin 1 ⊕ Fin d) (P : ℝ → Prop)
    (h : P ((A.1 * B.1) r c)) : P ((A * B).1 r c) := by
  simp only [lorentzGroupIsGroup_mul_coe]
  exact h

/-! ### R7. `Matrix.mul_apply` · `(M * N) r c = ∑ l, M r l * N l c` · goal -/
example {d : ℕ} (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (r c : Fin 1 ⊕ Fin d)
    (P : ℝ → Prop) (h : P (∑ l, M r l * N l c)) : P ((M * N) r c) := by
  simp only [Matrix.mul_apply]
  exact h

/-! ### R8. `Fintype.sum_sum_type` · a sum over `α ⊕ β` → a sum over `α` plus a sum over `β` · goal -/
example {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) (P : ℝ → Prop)
    (h : P (∑ a, f (Sum.inl a) + ∑ b, f (Sum.inr b))) : P (∑ x, f x) := by
  simp only [Fintype.sum_sum_type]
  exact h

/-! ### R9. `Fin.sum_univ_one` · `∑ a : Fin 1, f a = f 0` · goal (plain `simp` does this itself) -/
example (f : Fin 1 → ℝ) (P : ℝ → Prop) (h : P (f 0)) : P (∑ a, f a) := by
  rw [Fin.sum_univ_one]
  exact h

/-! ### R10. The `@[simp]` entries of `boost i β hβ` · goal: entries in time/axis-`i` positions
`boost_inl_0_inl_0`, `boost_inr_self_inr_self`, `boost_inl_0_inr_self`, `boost_inr_self_inl_0`.
Plain `simp` uses them by itself (and writes `-γ β * β` as `-(γ β * β)`). -/
example {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (P : ℝ → ℝ → ℝ → ℝ → Prop)
    (h : P (γ β) (γ β) (-γ β * β) (-γ β * β)) :
    P ((boost i β hβ).1 (Sum.inl 0) (Sum.inl 0)) ((boost i β hβ).1 (Sum.inr i) (Sum.inr i))
      ((boost i β hβ).1 (Sum.inl 0) (Sum.inr i)) ((boost i β hβ).1 (Sum.inr i) (Sum.inl 0)) := by
  simp only [boost_inl_0_inl_0, boost_inr_self_inr_self, boost_inl_0_inr_self, boost_inr_self_inl_0]
  exact h

/-! ### R11. `add_eq_left` · `a + b = a ↔ b = 0` · goal: drop a summand that both sides share
`simp` applies it by itself once the time term on the left equals the right side. -/
example (a b : ℝ) (h : b = 0) : a + b = a := by
  rw [add_eq_left]
  exact h

/-! ## A sum whose every term is zero -/

/-! ### R12. `apply Finset.sum_eq_zero` · goal: `∑ x ∈ s, f x = 0` → `∀ x ∈ s, f x = 0`
`∑ l, f l` is `∑ l ∈ Finset.univ, f l`, the sum over all of `Fin d`. -/
example {d : ℕ} (f : Fin d → ℝ) (h : ∀ l ∈ Finset.univ, f l = 0) : ∑ l, f l = 0 := by
  apply Finset.sum_eq_zero
  exact h

/-! ### R13. `intro l _` on `∀ x ∈ s, Q x` · context gains `l` and an unnamed `a✝ : l ∈ s` -/
example {d : ℕ} (Q : Fin d → Prop) (h : ∀ l, Q l) : ∀ l ∈ (Finset.univ : Finset (Fin d)), Q l := by
  intro l _
  exact h l

/-! ### R14. `by_cases hl : l = i` · goal list: two goals, with `hl : l = i` and `hl : ¬l = i` -/
example {d : ℕ} (l i : Fin d) (P : Prop) (k1 : l = i → P) (k2 : ¬l = i → P) : P := by
  by_cases hl : l = i
  · exact k1 hl
  · exact k2 hl

/-! ### R15. `subst hl` with `hl : l = i` · context: `i` is replaced by `l` everywhere, `hl` is used up -/
example {d : ℕ} (l i j : Fin d) (P : Fin d → Fin d → Prop) (hij : i ≠ j) (k : ∀ a, a ≠ j → P a a)
    (hl : l = i) : P l i := by
  subst hl
  exact k l hij

/-! ### R16. `boost_inr_other_inr hβ hj` · `j ≠ i → (boost i β hβ).1 (inr j) (inr k) = if j = k then 1 else 0`
Row `j ≠ i` of a boost along `i` is the row of the identity matrix. · goal -/
example {d : ℕ} (i j k : Fin d) (β : ℝ) (hβ : |β| < 1) (hj : j ≠ i) (P : ℝ → Prop)
    (h : P (if j = k then 1 else 0)) : P ((boost i β hβ).1 (Sum.inr j) (Sum.inr k)) := by
  rw [boost_inr_other_inr hβ hj]
  exact h

/-! ### R17. `simp [hne]` with `hne : a ≠ b` · goal: `if a = b then x else y` → `y` -/
example {d : ℕ} (a b : Fin d) (hne : a ≠ b) (x y : ℝ) (P : ℝ → Prop) (h : P y) :
    P (if a = b then x else y) := by
  simp [hne]
  exact h

/-! ### R18. `boost_inr_self_inr_other hβ hj` · `j ≠ i → (boost i β hβ).1 (inr i) (inr j) = 0` · goal -/
example {d : ℕ} (i j : Fin d) (β : ℝ) (hβ : |β| < 1) (hj : j ≠ i) (P : ℝ → Prop) (h : P 0) :
    P ((boost i β hβ).1 (Sum.inr i) (Sum.inr j)) := by
  rw [boost_inr_self_inr_other hβ hj]
  exact h

/-! ## Rows of the identity -/

/-! ### R19. `Ne.symm` · from `h : a ≠ b` get `b ≠ a` · context gains the flipped fact -/
example {d : ℕ} (a b : Fin d) (h : a ≠ b) (P : Prop) (k : b ≠ a → P) : P := by
  have h' : b ≠ a := Ne.symm h
  exact k h'

/-! ### R20. `boost_inr_other_inl_0 hβ hj` · `j ≠ i → (boost i β hβ).1 (inr j) (inl 0) = 0` · goal -/
example {d : ℕ} (i j : Fin d) (β : ℝ) (hβ : |β| < 1) (hj : j ≠ i) (P : ℝ → Prop) (h : P 0) :
    P ((boost i β hβ).1 (Sum.inr j) (Sum.inl 0)) := by
  rw [boost_inr_other_inl_0 hβ hj]
  exact h

/-! ### R21. `Finset.sum_ite_eq` (with `ite_mul`), via `simp` · goal: `∑ a, (if j = a then 1 else 0) * f a` → `f j`
A row of the identity picks out one term of the sum. -/
example {d : ℕ} (j : Fin d) (f : Fin d → ℝ) (P : ℝ → Prop) (h : P (f j)) :
    P (∑ a, (if j = a then 1 else 0) * f a) := by
  simp
  exact h

/-! ## From `=` to a contradiction -/

/-! ### R22. `intro h` on `a ≠ b` · `a ≠ b` means `a = b → False` · goal: `False`, context gains `h : a = b` -/
example {α : Type} (a b : α) (k : a = b → False) : a ≠ b := by
  intro h
  exact k h

/-! ### R23. `boost_transpose_matrix_eq_self i hβ` · `(↑(boost i β hβ))ᵀ = ↑(boost i β hβ)` · context
A boost's matrix is symmetric. Use it as a term, e.g. in `have`. -/
example {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (P : Prop) (k : (boost i β hβ).1ᵀ = (boost i β hβ).1 → P) :
    P := by
  have hs := boost_transpose_matrix_eq_self i hβ
  exact k hs

/-! ### R24. `congrFun (congrFun hM r) c` · from `hM : M = N` get `M r c = N r c` · context
`congrFun : f = g → ∀ a, f a = g a`; a matrix is a function of the row, then of the column. -/
example {d : ℕ} (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hM : M = N) (r c : Fin 1 ⊕ Fin d)
    (P : Prop) (k : M r c = N r c → P) : P := by
  have e := congrFun (congrFun hM r) c
  exact k e

/-! ### R25. `rw [← h] at e` with `h : a = b` · context: every `b` in `e` becomes `a` -/
example {α : Type} (a b : α) (Q : α → Prop) (h : a = b) (e : Q b) : Q a := by
  rw [← h] at e
  exact e

/-! ### R26. `simp only [transpose_apply] at e` · `Mᵀ r c = M c r` · context: `e` loses the `ᵀ` -/
example {d : ℕ} (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (r c : Fin 1 ⊕ Fin d)
    (e : Mᵀ r c = N r c) : M c r = N r c := by
  simp only [transpose_apply] at e
  exact e

/-! ### R27. `mul_ne_zero` · `a ≠ 0 → b ≠ 0 → a * b ≠ 0` · context gains the product fact -/
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (P : Prop) (k : a * b ≠ 0 → P) : P := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  exact k hab

/-! ### R28. `exact hne e.symm` · `hne : a ≠ 0`, `e : 0 = a` · closes `False`
`e.symm : a = 0` (`Eq.symm`), and `hne` applied to it is `False`. -/
example (a : ℝ) (hne : a ≠ 0) (e : 0 = a) : False := by
  exact hne e.symm

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One boost is symmetric entrywise: R23, R24, R26 -/
example {d : ℕ} (i j : Fin d) (β : ℝ) (hβ : |β| < 1) :
    (boost i β hβ).1 (Sum.inr j) (Sum.inl 0) = (boost i β hβ).1 (Sum.inl 0) (Sum.inr j) := by
  have e := congrFun (congrFun (boost_transpose_matrix_eq_self i hβ) (Sum.inl 0)) (Sum.inr j)
  simp only [transpose_apply] at e
  exact e

/-! ### W2. An entry of a boost squared, off the boosted axis: R6, R7, R8, then R20, R16, R21 -/
example {d : ℕ} (i j : Fin d) (hj : j ≠ i) (β : ℝ) (hβ : |β| < 1) :
    (boost i β hβ * boost i β hβ).1 (Sum.inr j) (Sum.inr j) = 1 := by
  simp only [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [boost_inr_other_inl_0 hβ hj, boost_inr_other_inr hβ hj]

/-! ### W3. A nonzero product cannot equal `0`: R27, R28 -/
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (e : 0 = a * b) : False := by
  have hne := mul_ne_zero ha hb
  exact hne e.symm

end H104Guide
