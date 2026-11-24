/- Guide for M143 (Correlations of the maximally entangled state; the 2√2 value).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other sums, √3, other vectors).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Pure.Braket

open Matrix
open scoped Kronecker

namespace M143Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · `mes_expect`: the two facts to prove first -/

/-! ### R1. `simp [Ket.MES]` · goal: an entry of the maximally entangled state → an `if`
`Ket.MES d : Ket (d × d)` is physlib's `Φ = Σᵢ |i⟩|i⟩ / √d`; `.vec : d × d → ℂ` is its vector of
amplitudes. Its definition is `fun (i, j) ↦ if i = j then 1 / √(card d) else 0`; `simp` unfolds it
and writes `1 / x` as `x⁻¹`. -/
example {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (i j : d) (P : ℂ → Prop)
    (h : P (if i = j then ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ else 0)) :
    P ((Ket.MES d).vec (i, j)) := by
  simp [Ket.MES]
  exact h

/-! ### R2. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; used right to left: `rw [← mul_inv]` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (P : α → Prop) (h : P (a * b)⁻¹) :
    P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R3. `Complex.ofReal_mul` · `↑(x * y) = ↑x * ↑y`; right to left moves `*` inside the cast -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ↑(x * y)) : P (↑x * ↑y) := by
  rw [← Complex.ofReal_mul]
  exact h

/-! ### R4. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal rewritten, plus side goal `0 ≤ x`
Here `x = ↑n`, a natural number cast into `ℝ`. -/
example (n : ℕ) (P : ℝ → Prop) (h : P n) : P (√(n : ℝ) * √(n : ℝ)) := by
  rw [Real.mul_self_sqrt]
  exact h
  exact Nat.cast_nonneg n

/-! ### R5. `Nat.cast_nonneg` · closes `0 ≤ ↑n` (a cast natural number is nonnegative)
Pass it straight to R4: `rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]`. -/
example (n : ℕ) : 0 ≤ (n : ℝ) := Nat.cast_nonneg n

/-! ### R6. `Complex.ofReal_natCast` · goal: `↑↑n` (ℕ → ℝ → ℂ) → `↑n` (ℕ → ℂ) -/
example (n : ℕ) (P : ℂ → Prop) (h : P (n : ℂ)) : P (((n : ℝ) : ℂ)) := by
  rw [Complex.ofReal_natCast]
  exact h

/-! ## Part 1 · `mes_expect`: from `⟨v|M|w⟩` to sums -/

/-! ### R7. `simp only [dotProduct, mulVec]` · goal: `v ⬝ᵥ M *ᵥ w` → a double sum
`M *ᵥ w` is the matrix–vector product, `(M *ᵥ w) x = ∑ y, M x y * w y`; `v ⬝ᵥ u = ∑ x, v x * u x`.
`v ⬝ᵥ M *ᵥ w` is read `v ⬝ᵥ (M *ᵥ w)`. -/
example {ι : Type} [Fintype ι] (v w : ι → ℂ) (M : Matrix ι ι ℂ) (P : ℂ → Prop)
    (h : P (∑ x, v x * ∑ y, M x y * w y)) : P (v ⬝ᵥ (M *ᵥ w)) := by
  simp only [dotProduct, mulVec]
  exact h

/-! ### R8. `Fintype.sum_prod_type` · goal: a sum over pairs `α × β` → a double sum -/
example {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℂ) (P : ℂ → Prop)
    (h : P (∑ x, ∑ y, f (x, y))) : P (∑ x, f x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R9. `Matrix.kroneckerMap_apply` · goal: entry of `A ⊗ₖ B` → a product of entries
`A ⊗ₖ B` is printed `kroneckerMap (fun x1 x2 => x1 * x2) A B`; rows and columns are pairs. -/
example {α β : Type} (A : Matrix α α ℂ) (B : Matrix β β ℂ) (i j : α) (k l : β) (P : ℂ → Prop)
    (h : P (A i j * B k l)) : P ((A ⊗ₖ B) (i, k) (j, l)) := by
  simp only [kroneckerMap_apply]
  exact h

/-! ### R10. `Pi.star_apply` · goal: `star v x` (conjugate the vector, then evaluate) → `star (v x)` -/
example {ι : Type} (v : ι → ℂ) (x : ι) (P : ℂ → Prop) (h : P (star (v x))) : P (star v x) := by
  rw [Pi.star_apply]
  exact h

/-! ### R11. `simp only [h]` with `h : ∀ i j, …` · goal: rewrites every instance, under binders too
`rw [h]` fails here: inside `∑ i, …` the term `f (i, j)` mentions the bound `i`, which `rw` cannot
instantiate. `simp only` can. -/
example {α : Type} [Fintype α] (f : α × α → ℂ) (g : α → α → ℂ) (hf : ∀ i j, f (i, j) = g i j)
    (P : ℂ → Prop) (h : P (∑ i, ∑ j, g i j)) : P (∑ i, ∑ j, f (i, j)) := by
  simp only [hf]
  exact h

/-! ## Part 1 · `mes_expect`: pushing `if` outward and collapsing sums -/

/-! ### R12. `apply_ite star`, then `star_zero` · goal: `star (if c then a else 0)` → `if c then star a else 0`
`apply_ite f : f (if c then x else y) = if c then f x else f y`; `star_zero : star 0 = 0`. -/
example (c : Prop) [Decidable c] (a : ℂ) (P : ℂ → Prop) (h : P (if c then star a else 0)) :
    P (star (if c then a else 0)) := by
  rw [apply_ite star]
  rw [star_zero]
  exact h

/-! ### R13. `mul_ite`, then `mul_zero` · goal: `a * (if c then b else 0)` → `if c then a * b else 0` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then a * b else 0)) :
    P (a * if c then b else 0) := by
  rw [mul_ite]
  rw [mul_zero]
  exact h

/-! ### R14. `ite_mul`, then `zero_mul` · goal: `(if c then a else 0) * b` → `if c then a * b else 0` -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then a * b else 0)) :
    P ((if c then a else 0) * b) := by
  rw [ite_mul]
  rw [zero_mul]
  exact h

/-! ### R15. `Finset.sum_ite_eq`, `Finset.mem_univ`, `if_true` · goal: `∑ j, if i = j then f j else 0` → `f i`
`Finset.sum_ite_eq : ∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0`.
`∑ j, …` is `∑ j ∈ Finset.univ, …`, and `Finset.mem_univ i : i ∈ Finset.univ` (`Finset.univ` is the
set of all elements of a finite type). For `if j = i` use `Finset.sum_ite_eq'`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (f : ι → ℂ) (P : ℂ → Prop) (h : P (f i)) :
    P (∑ j, if i = j then f j else 0) := by
  simp only [Finset.sum_ite_eq]
  simp only [Finset.mem_univ]
  simp only [if_true]
  exact h

/-! ### R16. `Complex.star_def`, `map_inv₀`, `Complex.conj_ofReal` · goal: `star (↑r)⁻¹` → `(↑r)⁻¹`
On `ℂ`, `star` is complex conjugation, printed `(starRingEnd ℂ) z`. `map_inv₀ : f a⁻¹ = (f a)⁻¹`
for a ring map `f`; `Complex.conj_ofReal : conj ↑r = ↑r`. -/
example (r : ℝ) (P : ℂ → Prop) (h : P (r : ℂ)⁻¹) : P (star (r : ℂ)⁻¹) := by
  simp only [Complex.star_def]
  simp only [map_inv₀]
  simp only [Complex.conj_ofReal]
  exact h

/-! ## Part 1 · `mes_expect`: comparing the two sides sum by sum -/

/-! ### R17. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal: factor moves into the sum -/
example {ι : Type} [Fintype ι] (a : ℂ) (f : ι → ℂ) (P : ℂ → Prop) (h : P (∑ i, a * f i)) :
    P (a * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R18. `refine Finset.sum_congr rfl fun i _ => ?_` · goal `∑ f = ∑ g` → `f i = g i` for a new `i`
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. -/
example {ι : Type} [Fintype ι] (f g : ι → ℂ) (h : ∀ i, f i = g i) : ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact h i

/-! ## Part 2 · `bell_chsh`: linearity -/

/-! ### R19. `Matrix.add_mulVec`, `Matrix.sub_mulVec` · goal: `(M + N - K) *ᵥ v` → three products -/
example {ι : Type} [Fintype ι] (M N K : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P (M *ᵥ v + N *ᵥ v - K *ᵥ v)) : P ((M + N - K) *ᵥ v) := by
  simp only [add_mulVec, sub_mulVec]
  exact h

/-! ### R20. `dotProduct_add`, `dotProduct_sub` · goal: `u ⬝ᵥ (v + w - x)` → three dot products -/
example {ι : Type} [Fintype ι] (u v w x : ι → ℂ) (P : ℂ → Prop)
    (h : P (u ⬝ᵥ v + u ⬝ᵥ w - u ⬝ᵥ x)) : P (u ⬝ᵥ (v + w - x)) := by
  simp only [dotProduct_add, dotProduct_sub]
  exact h

/-! ## Part 2 · `bell_chsh`: facts about `√2` -/

/-! ### R21. `Complex.ofReal_pow` · `↑(x ^ n) = ↑x ^ n`; right to left moves `^` inside the cast -/
example (x : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P ↑(x ^ n)) : P (↑x ^ n) := by
  rw [← Complex.ofReal_pow]
  exact h

/-! ### R22. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ### R23. `Complex.ofReal_ofNat` · goal: `↑3` (the real numeral cast into `ℂ`) → `3` -/
example (P : ℂ → Prop) (h : P 3) : P ((3 : ℝ) : ℂ) := by
  rw [Complex.ofReal_ofNat]
  exact h

/-! ### R24. `simp` · closes `↑√3 ≠ 0`
It uses `Complex.ofReal_eq_zero : ↑r = 0 ↔ r = 0` and `Real.sqrt_eq_zero : 0 ≤ x → (√x = 0 ↔ x = 0)`. -/
example : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by simp

/-! ## Part 2 · `bell_chsh`: evaluating 2×2 sums -/

/-! ### R25. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R26. `Fintype.card_fin` · goal: `Fintype.card (Fin n)` (the number of elements) → `n` -/
example (n : ℕ) (P : ℂ → Prop) (h : P (n : ℂ)) : P ((Fintype.card (Fin n) : ℂ)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R27. `Matrix.smul_apply`, `Matrix.add_apply`, `Matrix.sub_apply`, `smul_eq_mul` · goal:
entry of `c • (M + N - K)` → `c * (M i j + N i j - K i j)` -/
example {ι : Type} (c : ℂ) (M N K : Matrix ι ι ℂ) (i j : ι) (P : ℂ → Prop)
    (h : P (c * (M i j + N i j - K i j))) : P ((c • (M + N - K)) i j) := by
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  exact h

/-! ### R28. Entry of a literal `!![a, b; c, d] i j` (`simp`) · goal: → the entry itself -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P c) : P (!![a, b; c, d] 1 0) := by
  simp
  exact h

/-! ## Part 2 · `bell_chsh`: finishing an equation with `√2` -/

/-! ### R29. `field_simp` · goal: multiplies out the denominators it can prove nonzero
It finds `hx : x ≠ 0` in the context. What is left has no `⁻¹` and no `/`. -/
example (x y : ℂ) (hx : x ≠ 0) (h : 1 + 1 = 2 * x * y) : 2⁻¹ * (x⁻¹ + x⁻¹) = y := by
  field_simp
  exact h

/-! ### R30. `linear_combination c * h` · closes `a = b` when `a - b - c * (lhs_h - rhs_h)` is 0 by `ring` -/
example (x : ℂ) (h : x ^ 2 = 3) : 2 * x ^ 2 = 6 := by linear_combination 2 * h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Collapse a sum whose terms vanish off the diagonal: R14, then R15 -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℂ) (g : ι → ℂ) :
    ∑ i, ∑ j, (if i = j then f i j else 0) * g j = ∑ i, f i i * g i := by
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ### W2. Linearity of an expectation value `⟨v|M + N|v⟩`: R19, then R20 -/
example {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ ((M + N) *ᵥ v) = star v ⬝ᵥ (M *ᵥ v) + star v ⬝ᵥ (N *ᵥ v) := by
  simp only [add_mulVec]
  simp only [dotProduct_add]

/-! ### W3. The `√3` fact as one chain: R21, R22, R23 -/
example : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num)]
  rw [Complex.ofReal_ofNat]

/-! ### W4. Finishing with `field_simp` and `linear_combination`: R24, R29, R30 -/
example : (3 : ℂ)⁻¹ * (↑√3 + ↑√3 + ↑√3) = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * 3 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    simp
  have hne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by simp
  field_simp
  linear_combination 3 * h3

end M143Guide
