/- Guide for M128 (Eigenvalues of involutions).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (an idempotent, `Mᴴ`, `3 * x`).
Assumed: Lean basics.
-/
import Mathlib

open Matrix

namespace M128Guide

/-! # Part R · Reference entries -/

/-! ## Unitary and Hermitian: from a name to an equation -/

/-! ### R1. `Matrix.mem_unitaryGroup_iff` · context: membership `hM` → an equation
`rw [lemma] at hM` rewrites the hypothesis `hM` instead of the goal. -/
example {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (G : Prop)
    (hM : M ∈ Matrix.unitaryGroup n ℂ) (h : M * star M = 1 → G) : G := by
  rw [Matrix.mem_unitaryGroup_iff] at hM
  exact h hM

/-! ### R2. `Matrix.star_eq_conjTranspose` · context (or goal): `star M` → `Mᴴ` -/
example {n : Type} (M : Matrix n n ℂ) (Q : Matrix n n ℂ → Prop) (G : Prop)
    (hM : Q (star M)) (h : Q Mᴴ → G) : G := by
  rw [Matrix.star_eq_conjTranspose] at hM
  exact h hM

/-! ### R3. `Matrix.IsHermitian.eq` · `hA.eq : Aᴴ = A` for `hA : A.IsHermitian`; goal: `Aᴴ` → `A` -/
example {n : Type} (A : Matrix n n ℂ) (hA : A.IsHermitian) (Q : Matrix n n ℂ → Prop) (h : Q A) :
    Q Aᴴ := by
  rw [hA.eq]
  exact h

/-! ## Matrix times vector -/

/-! ### R4. `Matrix.mulVec_mulVec` · goal: `M *ᵥ (N *ᵥ v)` → `(M * N) *ᵥ v`
Lean prints `M *ᵥ (N *ᵥ v)` as `M *ᵥ N *ᵥ v`: `*ᵥ` groups to the right. -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P ((M * N) *ᵥ v)) : P (M *ᵥ (N *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec]
  exact h

/-! ### R5. `Matrix.one_mulVec` · goal: `1 *ᵥ v` → `v` (`1` is the identity matrix) -/
example {n : Type} [Fintype n] [DecidableEq n] (v : n → ℂ) (P : (n → ℂ) → Prop) (h : P v) :
    P ((1 : Matrix n n ℂ) *ᵥ v) := by
  rw [Matrix.one_mulVec]
  exact h

/-! ### R6. `Matrix.mulVec_smul` · goal: `M *ᵥ (b • v)` → `b • (M *ᵥ v)` (pull a scalar out)
Lean prints these as `M *ᵥ b • v` and `b • M *ᵥ v`. -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (b : ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P (b • (M *ᵥ v))) : P (M *ᵥ (b • v)) := by
  rw [Matrix.mulVec_smul]
  exact h

/-! ## Scalars acting on vectors -/

/-! ### R7. `smul_smul` · goal: `a • b • x` → `(a * b) • x` -/
example {R V : Type} [Monoid R] [MulAction R V] (a b : R) (x : V) (P : V → Prop)
    (h : P ((a * b) • x)) : P (a • b • x) := by
  rw [smul_smul]
  exact h

/-! ### R8. `sub_smul` · goal: `(r - s) • x` → `r • x - s • x` -/
example {R V : Type} [Ring R] [AddCommGroup V] [Module R V] (r s : R) (x : V) (P : V → Prop)
    (h : P (r • x - s • x)) : P ((r - s) • x) := by
  rw [sub_smul]
  exact h

/-! ### R9. `one_smul` · goal: `1 • x` → `x` -/
example {R V : Type} [Monoid R] [MulAction R V] (x : V) (P : V → Prop) (h : P x) :
    P ((1 : R) • x) := by
  rw [one_smul]
  exact h

/-! ### R10. `sub_self` · goal: `a - a` → `0`
When `rw` leaves `0 = 0` (or any `t = t`), it closes the goal by itself with `rfl`. -/
example {V : Type} [AddGroup V] (a : V) (P : V → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! ## Products that vanish, and case splits -/

/-! ### R11. `smul_eq_zero` · `r • x = 0 ↔ r = 0 ∨ x = 0`; `.mp` turns `hx` into the `∨` -/
example {n : Type} (r : ℂ) (x : n → ℂ) (hx : r • x = 0) (G : Prop) (h : r = 0 ∨ x = 0 → G) :
    G := by
  have h2 := smul_eq_zero.mp hx
  exact h h2

/-! ### R12. `rcases h with h1 | h2` · goal list: one goal per side of `h : A ∨ B` -/
example (A B G : Prop) (hAB : A ∨ B) (ha : A → G) (hb : B → G) : G := by
  rcases hAB with h1 | h2
  exacts [ha h1, hb h2]

/-! ### R13. `linear_combination e` · closes `a = b` when `a - b` equals `c · (lhs - rhs of e)` by `ring`
Here `e = h` (coefficient 1); `linear_combination -h` or `2 * h` scales it. -/
example {α : Type} [CommRing α] (a b : α) (h : a * a - b * b = 0) : (a - b) * (a + b) = 0 := by
  linear_combination h

/-! ### R14. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp` turns `hab` into the `∨` -/
example (a b : ℂ) (hab : a * b = 0) (G : Prop) (h : a = 0 ∨ b = 0 → G) : G := by
  have h2 := mul_eq_zero.mp hab
  exact h h2

/-! ### R15. `left` / `right` · goal: `A ∨ B` → `A` (left) or `B` (right) -/
example (A B : Prop) (ha : A) : A ∨ B := by
  left
  exact ha

example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R16. `exact absurd ha hna` · closes any goal from `ha : A` and `hna : ¬A`
`x ≠ y` is notation for `¬(x = y)`, so `hv : v ≠ 0` is a valid `hna` for `ha : v = 0`. -/
example (A G : Prop) (ha : A) (hna : ¬A) : G := by
  exact absurd ha hna

/-! ## Inner products: `star v ⬝ᵥ w` -/

/-! ### R17. `Matrix.star_mulVec` · goal: `star (M *ᵥ v)` → `star v ᵥ* Mᴴ` (row vector times matrix) -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P (star v ᵥ* Mᴴ)) : P (star (M *ᵥ v)) := by
  rw [Matrix.star_mulVec]
  exact h

/-! ### R18. `Matrix.dotProduct_mulVec` · goal: `u ⬝ᵥ (A *ᵥ w)` → `(u ᵥ* A) ⬝ᵥ w` (move `A` left)
Lean prints these as `u ⬝ᵥ A *ᵥ w` and `u ᵥ* A ⬝ᵥ w`. -/
example {n : Type} [Fintype n] (u w : n → ℂ) (A : Matrix n n ℂ) (P : ℂ → Prop)
    (h : P ((u ᵥ* A) ⬝ᵥ w)) : P (u ⬝ᵥ (A *ᵥ w)) := by
  rw [Matrix.dotProduct_mulVec]
  exact h

/-! ### R19. `dotProduct_neg` · goal: `u ⬝ᵥ -w` → `-(u ⬝ᵥ w)` -/
example {n : Type} [Fintype n] (u w : n → ℂ) (P : ℂ → Prop) (h : P (-(u ⬝ᵥ w))) :
    P (u ⬝ᵥ -w) := by
  rw [dotProduct_neg]
  exact h

/-! ### R20. `simpa using e` · closes the goal: simplifies `e` and the goal, then matches them
`simp` knows `3 * x = 0 ↔ x = 0` in `ℂ` (it uses `mul_eq_zero` and `3 ≠ 0`). -/
example (x : ℂ) (h : 3 * x = 0) : x = 0 := by
  simpa using h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An eigenvector of `M` is one of `M * M`: R4 backwards, R6, R7 -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) (c : ℂ) (h : M *ᵥ v = c • v) :
    (M * M) *ᵥ v = (c * c) • v := by
  rw [← Matrix.mulVec_mulVec]
  rw [h]
  rw [Matrix.mulVec_smul]
  rw [h]
  rw [smul_smul]

/-! ### W2. The adjoint moves across the inner product: R17, R18 (no Hermitian needed) -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v w : n → ℂ) :
    star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (Mᴴ *ᵥ w) := by
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]

/-! ### W3. Idempotent scalars are `0` or `1`: R13, R12 with R14, R15 -/
example (z : ℂ) (h : z * z = z) : z = 0 ∨ z = 1 := by
  have h2 : z * (z - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    exact h3
  · right
    linear_combination h3

/-! ### W4. From `x = 3 * x` to `x = 0`: R13 with a coefficient, then R20 -/
example (x : ℂ) (h : x = 3 * x) : x = 0 := by
  have h2 : (2 : ℂ) * x = 0 := by linear_combination -h
  simpa using h2

end M128Guide
