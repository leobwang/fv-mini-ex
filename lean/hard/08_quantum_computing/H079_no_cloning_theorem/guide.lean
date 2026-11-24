/- Guide for H079 (The no-cloning theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (plain sums, a matrix with a left
inverse, a quadratic other than `z = z * z`).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.Operators.Unitary

open scoped Matrix

namespace H079Guide

open Braket

/-! # Part R · Reference entries -/

/-! ## Bra-kets → sums of entries (MILESTONE `dot_eq_star_dotProduct`) -/

/-! ### R1. `simp only [Braket.dot]` · goal: `〈ψ‖φ〉` → the sum `∑ x, ↑ψ x * φ x`
The infoview prints `〈ψ‖φ〉` as `dot (↑ψ) φ`; `↑ψ` is the bra of `ψ` (`Ket.to_bra ψ`).
A bra can be applied to an index `x : d` or to a ket, so to write "the bra's entry at `x`" by hand
this file names the instance (`Braket.instFunLikeBra`); you never need to in the exercise. -/
example {d : Type} [Fintype d] (ψ φ : Ket d) (P : ℂ → Prop)
    (h : P (∑ x : d, @DFunLike.coe _ _ _ Braket.instFunLikeBra (Ket.to_bra ψ) x * φ x)) :
    P 〈ψ‖φ〉 := by
  simp only [Braket.dot]
  exact h

/-! ### R2. `simp only [Ket.to_bra]`, then `simp only [Bra.apply]` · goal: an entry of the bra `↑ψ`
→ an entry of the conjugated function `(starRingEnd (d → ℂ)) ⇑ψ` (`⇑ψ` is `ψ` seen as `d → ℂ`) -/
example {d : Type} [Fintype d] (ψ : Ket d) (x : d) (P : ℂ → Prop)
    (h : P ((starRingEnd (d → ℂ)) (ψ : d → ℂ) x)) :
    P (@DFunLike.coe _ _ _ Braket.instFunLikeBra (Ket.to_bra ψ) x) := by
  simp only [Ket.to_bra]
  simp only [Bra.apply]
  exact h

/-! ### R3. `Pi.conj_apply` · goal: conjugate of a function, evaluated → conjugate of the value -/
example {d : Type} (v : d → ℂ) (x : d) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) (v x))) :
    P ((starRingEnd (d → ℂ)) v x) := by
  rw [Pi.conj_apply]
  exact h

/-! ### R4. `Ket.apply` · goal: `ψ x` (a ket used as a function) → `ψ.vec x` (its field) -/
example {d : Type} [Fintype d] (ψ : Ket d) (x : d) (P : ℂ → Prop) (h : P (ψ.vec x)) : P (ψ x) := by
  rw [Ket.apply]
  exact h

/-! ### R5. `simp only [dotProduct]` · goal: `v ⬝ᵥ w` → `∑ i, v i * w i` -/
example {d : Type} [Fintype d] (v w : d → ℂ) (P : ℂ → Prop) (h : P (∑ i, v i * w i)) :
    P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R6. `Pi.star_apply`, then `RCLike.star_def` · goal: `star v i` → `star (v i)` → `conj (v i)`
`star` on `ℂ` is complex conjugation; `RCLike.star_def` writes it as `starRingEnd ℂ`. -/
example {d : Type} (v : d → ℂ) (i : d) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) (v i))) :
    P (star v i) := by
  rw [Pi.star_apply]
  rw [RCLike.star_def]
  exact h

/-! ## Sums over pairs (MILESTONE `dot_prod`) -/

/-! ### R7. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (g : α × β → M) (P : M → Prop)
    (h : P (∑ a, ∑ b, g (a, b))) : P (∑ x, g x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R8. `Finset.sum_mul_sum` · goal: a product of two sums → a double sum of products -/
example {α β R : Type} [Fintype α] [Fintype β] [NonUnitalNonAssocSemiring R] (f : α → R) (g : β → R)
    (P : R → Prop) (h : P (∑ i, ∑ j, f i * g j)) : P ((∑ i, f i) * ∑ j, g j) := by
  rw [Finset.sum_mul_sum]
  exact h

/-! ### R9. `refine Finset.sum_congr rfl fun i _ => ?_` · goal: equal sums → equal summands
Context gains `i` and `x✝ : i ∈ Finset.univ` (the index ranges over all of `α`). Nest it for a
double sum: `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_`. -/
example {α M : Type} [Fintype α] [AddCommMonoid M] (f g : α → M) (h : ∀ i, f i = g i) :
    ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact h i

/-! ### R10. `simp only [Ket.prod, Ket.apply]` · goal: an entry of `ψ ⊗ᵠ φ` → a product of entries -/
example {d : Type} [Fintype d] (ψ φ : Ket d) (i j : d) (P : ℂ → Prop)
    (h : P (ψ.vec i * φ.vec j)) : P ((ψ ⊗ᵠ φ) (i, j)) := by
  simp only [Ket.prod, Ket.apply]
  exact h

/-! ### R11. `map_mul` · goal: `conj (a * b)` → `conj a * conj b` (conjugation is multiplicative) -/
example (a b : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)) :
    P ((starRingEnd ℂ) (a * b)) := by
  rw [map_mul]
  exact h

/-! ## Moving a matrix across a dot product (MILESTONE `unitary_dot`) -/

/-! ### R12. `Matrix.star_mulVec` · goal: `star (M *ᵥ v)` → `star v ᵥ* Mᴴ` -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P (star v ᵥ* Mᴴ)) : P (star (M *ᵥ v)) := by
  rw [Matrix.star_mulVec]
  exact h

/-! ### R13. `Matrix.dotProduct_mulVec` · goal: `v ⬝ᵥ (A *ᵥ w)` → `(v ᵥ* A) ⬝ᵥ w` -/
example {n : Type} [Fintype n] (A : Matrix n n ℂ) (v w : n → ℂ) (P : ℂ → Prop)
    (h : P (v ᵥ* A ⬝ᵥ w)) : P (v ⬝ᵥ (A *ᵥ w)) := by
  rw [Matrix.dotProduct_mulVec]
  exact h

/-! ### R14. `Matrix.vecMul_vecMul` · goal: `v ᵥ* M ᵥ* N` → `v ᵥ* (M * N)` -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P (v ᵥ* (M * N))) : P (v ᵥ* M ᵥ* N) := by
  rw [Matrix.vecMul_vecMul]
  exact h

/-! ### R15. `rw [← Matrix.star_eq_conjTranspose]` · goal: `Mᴴ` → `star M` -/
example {n : Type} (M : Matrix n n ℂ) (P : Matrix n n ℂ → Prop) (h : P (star M)) : P Mᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact h

/-! ### R16. `Matrix.UnitaryGroup.star_mul_self` · goal: `star ↑U * ↑U` → `1` for `U : 𝐔[n]`
`↑U` (also written `U.val`) is the matrix underneath the unitary `U`. -/
example {n : Type} [Fintype n] [DecidableEq n] (U : 𝐔[n]) (P : Matrix n n ℂ → Prop) (h : P 1) :
    P (star U.val * U.val) := by
  rw [Matrix.UnitaryGroup.star_mul_self]
  exact h

/-! ### R17. `Matrix.vecMul_one` · goal: `v ᵥ* 1` → `v` -/
example {n : Type} [Fintype n] [DecidableEq n] (v : n → ℂ) (P : (n → ℂ) → Prop) (h : P v) :
    P (v ᵥ* (1 : Matrix n n ℂ)) := by
  rw [Matrix.vecMul_one]
  exact h

/-! ## From `z * 1 = z * z` to `z = 0 ∨ z = 1` (the main theorem) -/

/-! ### R18. `rw [← L]` where `L` has arguments · goal: the FIRST match fixes the arguments
`mul_add : a * (b + c) = a * b + a * c`. Right to left, `rw` looks for `?a * ?b + ?a * ?c`; the first
match sets `?a := x` and rewrites only that instance; a second `rw [← mul_add]` takes the next one. -/
example {R : Type} [CommRing R] (x y z w : R) (P : R → R → Prop)
    (h : P (x * (y + z)) (w * (y + z))) : P (x * y + x * z) (w * y + w * z) := by
  rw [← mul_add]
  rw [← mul_add]
  exact h

/-! ### R19. `rw [Braket.dot_self_eq_one] at h` · context: `〈f‖f〉` inside `h` → `1` -/
example {d : Type} [Fintype d] (f : Ket d) (P : ℂ → Prop) (h : P 〈f‖f〉) : P 1 := by
  rw [Braket.dot_self_eq_one] at h
  exact h

/-! ### R20. `linear_combination e` · closes `a = b` when `a - b` equals `e`'s `lhs - rhs` by `ring`
Here `-h` contributes `-(a - b)`, and `b - a - 0 = -(a - b)` holds by `ring`. -/
example {R : Type} [CommRing R] (a b : R) (h : a = b) : b - a = 0 := by
  linear_combination -h

/-! ### R21. `rcases mul_eq_zero.mp h with h | h` · context `h : a * b = 0` → two goals,
one with `h : a = 0`, one with `h : b = 0`. Needs a ring without zero divisors (`ℂ`, `ℝ`). -/
example (a b : ℂ) (G : Prop) (h : a * b = 0) (ga : a = 0 → G) (gb : b = 0 → G) : G := by
  rcases mul_eq_zero.mp h with h | h
  · exact ga h
  · exact gb h

/-! ### R22. `sub_eq_zero.mp` · `a - b = 0 → a = b` · closes the goal `a = b` -/
example {R : Type} [CommRing R] (a b : R) (h : a - b = 0) : a = b := by
  exact sub_eq_zero.mp h

/-! ### R23. `Or.inl`, `Or.inr` · close `A ∨ B` from a proof of `A` (resp. `B`) -/
example (A B : Prop) (hb : B) : A ∨ B := by
  exact Or.inr hb

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A sum over pairs of a product factors: R7, then R8 backwards -/
example {d : Type} [Fintype d] (a b : d → ℂ) :
    ∑ x : d × d, a x.1 * b x.2 = (∑ i, a i) * ∑ j, b j := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-! ### W2. Combine two matrices, substitute a fact, drop the identity
(the shape of the `unitary_dot` chain, with `*ᵥ` and a left inverse instead of `ᵥ*` and `𝐔[n]`) -/
example {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hAB : A * B = 1) (x : n → ℂ) :
    A *ᵥ (B *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec]
  rw [hAB]
  rw [Matrix.one_mulVec]

/-! ### W3. A quadratic fact → a disjunction: R20, R21, R22, R23 -/
example (z : ℂ) (key : z * 2 = z * z) : z = 0 ∨ z = 2 := by
  have h : z * (z - 2) = 0 := by linear_combination -key
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

end H079Guide
