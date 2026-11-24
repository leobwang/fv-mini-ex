/- Guide for E112 (Kets and bra-kets).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the ket (3/5)|0⟩ + (4/5)|1⟩, √3).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Pure.Braket

open Braket

namespace E112Guide

/-! # Part R · Reference entries -/

/-! ## A bra-ket → a sum of entries -/

/-! ### R1. `Braket.dot` · goal: `〈φ‖ψ〉` → `∑ x, ↑φ x * ψ x`
`〈φ‖ψ〉` is notation for `dot ↑φ ψ`; `↑φ` is the ket `φ` turned into a bra (R2). -/
example {d : Type} [Fintype d] (φ ψ : Ket d) (P : ℂ → Prop)
    (h : P (∑ x, ((φ : Bra d) : d → ℂ) x * ψ x)) : P 〈φ‖ψ〉 := by
  simp only [Braket.dot]
  exact h

/-! ### R2. `Ket.to_bra` · goal: the bra `↑φ` → a structure literal whose vector is `conj ⇑φ`
`(starRingEnd (d → ℂ)) ⇑φ` is the vector `φ` with every entry complex-conjugated (R4). -/
example {d : Type} [Fintype d] (φ : Ket d) (x : d) (P : ℂ → Prop)
    (h : P ((starRingEnd (d → ℂ)) ⇑φ x)) : P (((φ : Bra d) : d → ℂ) x) := by
  simp only [Ket.to_bra]
  exact h

/-! ### R3. `Bra.apply`, `Ket.apply` · goal: `ξ x` → `ξ.vec x`; on a literal, straight to `v x` -/
example {d : Type} [Fintype d] (ψ : Ket d) (x : d) (P : ℂ → Prop) (h : P (ψ.vec x)) :
    P (ψ x) := by
  simp only [Ket.apply]
  exact h

example {d : Type} [Fintype d] (v : d → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) (x : d) (P : ℂ → Prop)
    (h : P (v x)) : P (((⟨v, hv⟩ : Bra d) : d → ℂ) x) := by
  simp only [Bra.apply]
  exact h

/-! ### R4. `Pi.conj_apply` · goal: entry `x` of a conjugated vector → conjugate of entry `x` -/
example {d : Type} (f : d → ℂ) (x : d) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) (f x))) :
    P ((starRingEnd (d → ℂ)) f x) := by
  simp only [Pi.conj_apply]
  exact h

/-! ### R5. `Ket.basis` · goal: `Ket.basis i` → its literal; with R3, entry `x` → `if i = x then 1 else 0`
physlib decides `i = x` classically, so the `if` here uses `Classical.propDecidable` (see R12). -/
open Classical in
example {d : Type} [Fintype d] (i x : d) (P : ℂ → Prop) (h : P (if i = x then 1 else 0)) :
    P (Ket.basis i x) := by
  simp only [Ket.basis]
  simp only [Ket.apply]
  exact h

/-! ## Evaluating the sum (`simp` applies these by itself) -/

/-! ### R6. `MonoidWithZeroHom.map_ite_one_zero` · goal: `conj (if p then 1 else 0)` → `if p then 1 else 0` -/
example (p : Prop) [Decidable p] (P : ℂ → Prop) (h : P (if p then 1 else 0)) :
    P ((starRingEnd ℂ) (if p then 1 else 0)) := by
  rw [MonoidWithZeroHom.map_ite_one_zero]
  exact h

/-! ### R7. `mul_ite` · goal: `a * (if p then b else c)` → `if p then a * b else a * c` -/
example {α : Type} [Mul α] (p : Prop) [Decidable p] (a b c : α) (P : α → Prop)
    (h : P (if p then a * b else a * c)) : P (a * if p then b else c) := by
  rw [mul_ite]
  exact h

/-! ### R8. `ite_mul` · goal: `(if p then a else b) * c` → `if p then a * c else b * c` -/
example {α : Type} [Mul α] (p : Prop) [Decidable p] (a b c : α) (P : α → Prop)
    (h : P (if p then a * c else b * c)) : P ((if p then a else b) * c) := by
  rw [ite_mul]
  exact h

/-! ### R9. `mul_one`, `mul_zero` (and `one_mul`, `zero_mul`) · goal: drop the factors `1` and `0` -/
example {α : Type} [MulZeroOneClass α] (p : Prop) [Decidable p] (a : α) (P : α → Prop)
    (h : P (if p then a else 0)) : P (if p then a * 1 else a * 0) := by
  rw [mul_one, mul_zero]
  exact h

/-! ### R10. `Finset.sum_ite_eq` · goal: a sum with one nonzero term → that term
`∑ x, if a = x then b x else 0 = if a ∈ Finset.univ then b a else 0`. The variant
`Finset.sum_ite_eq'` is for `if x = a`. -/
example {d : Type} [Fintype d] [DecidableEq d] (a : d) (b : d → ℂ) (P : ℂ → Prop)
    (h : P (if a ∈ Finset.univ then b a else 0)) : P (∑ x, if a = x then b x else 0) := by
  rw [Finset.sum_ite_eq]
  exact h

/-! ### R11. `Finset.mem_univ`, then `↓reduceIte` · goal: `if a ∈ Finset.univ then u else v` → `u` -/
example {α : Type} {d : Type} [Fintype d] [DecidableEq d] (a : d) (u v : α) (P : α → Prop)
    (h : P u) : P (if a ∈ Finset.univ then u else v) := by
  simp only [Finset.mem_univ]
  simp only [↓reduceIte]
  exact h

/-! ### R12. `ite_eq_ite` · closes `(if p then x else y) = if p then x else y`, even when the two
`if`s decide `p` with different instances (classical vs `DecidableEq`), where `rfl` fails. -/
example {α : Type} (p : Prop) (h₁ h₂ : Decidable p) (x y : α) :
    @ite α p h₁ x y = @ite α p h₂ x y := by
  simp only [ite_eq_ite]

/-! ## Building a ket -/

/-! ### R13. Anonymous constructor `⟨v, ?_⟩` · goal `Ket d` → the normalization goal
`Ket d` is a structure with fields `vec : d → ℂ` and `normalized' : ∑ x, ‖vec x‖ ^ 2 = 1`. In
term mode write `⟨v, by tac⟩`; `tac` sees the same goal. -/
example {d : Type} [Fintype d] (v : d → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) : Ket d := by
  refine ⟨v, ?_⟩
  exact hv

/-! ## The normalization sum (`simp` applies these by itself) -/

/-! ### R14. `norm_inv` · `‖a⁻¹‖ = ‖a‖⁻¹` -/
example {α : Type} [NormedDivisionRing α] (a : α) (P : ℝ → Prop) (h : P ‖a‖⁻¹) : P ‖a⁻¹‖ := by
  rw [norm_inv]
  exact h

/-! ### R15. `Complex.norm_real` · `‖(↑r : ℂ)‖ = ‖r‖` (norm of a real number cast into `ℂ`) -/
example (r : ℝ) (P : ℝ → Prop) (h : P ‖r‖) : P ‖(r : ℂ)‖ := by
  rw [Complex.norm_real]
  exact h

/-! ### R16. `Real.norm_eq_abs` · `‖r‖ = |r|` for `r : ℝ` -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R17. `inv_pow` · `a⁻¹ ^ n = (a ^ n)⁻¹` -/
example {α : Type} [DivisionMonoid α] (a : α) (n : ℕ) (P : α → Prop) (h : P (a ^ n)⁻¹) :
    P (a⁻¹ ^ n) := by
  rw [inv_pow]
  exact h

/-! ### R18. `sq_abs` · `|a| ^ 2 = a ^ 2` -/
example (a : ℝ) (P : ℝ → Prop) (h : P (a ^ 2)) : P (|a| ^ 2) := by
  rw [sq_abs]
  exact h

/-! ### R19. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · goal rewritten, plus side goal `0 ≤ x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt]
  exact h
  exact hx

/-! ### R20. `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin` · goal: a constant sum → `n • c` -/
example {β : Type} [AddCommMonoid β] (n : ℕ) (c : β) (P : β → Prop) (h : P (n • c)) :
    P (∑ _x : Fin n, c) := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  exact h

/-! ### R21. `nsmul_eq_mul`, then `Nat.cast_ofNat` · goal: `2 • c` → `↑2 * c` → `2 * c` -/
example (c : ℝ) (P : ℝ → Prop) (h : P (2 * c)) : P ((2 : ℕ) • c) := by
  rw [nsmul_eq_mul]
  rw [Nat.cast_ofNat]
  exact h

/-! ### R22. `mul_inv_cancel₀` · `a ≠ 0 → a * a⁻¹ = 1` · goal closed, side goal `a ≠ 0` -/
example {α : Type} [GroupWithZero α] (a : α) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul_inv_cancel₀]
  exact ha

/-! ## Reading off a ket's entries -/

/-! ### R23. `rfl` · closes an equation that holds by unfolding definitions
An entry of a literal ket is its vector's entry by definition (that is what `Ket.apply` says). `rfl`
also unfolds names you defined, so `ψ i = v i` holds for `def ψ : Ket d := ⟨v, _⟩`. -/
example {d : Type} [Fintype d] (v : d → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) (i : d) :
    (⟨v, hv⟩ : Ket d) i = v i := by
  rfl

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- The qubit state (3/5)|0⟩ + (4/5)|1⟩. `![a, b]` is the vector with entries `a, b`. -/
noncomputable def q : Ket (Fin 2) := ⟨![3 / 5, 4 / 5], by simp [Fin.sum_univ_two]; norm_num⟩

/-! ### W1. Reading an entry: R23 -/
example : q 1 = 4 / 5 := rfl

/-! ### W2. A bra-ket step by step: R1, (R2, R5), R3, R4, R3, R6, (R8, R9), R10, R11 -/
example : 〈Ket.basis (1 : Fin 2)‖q〉 = 4 / 5 := by
  simp only [Braket.dot]
  simp only [Ket.to_bra, Ket.basis, q]
  simp only [Bra.apply, Ket.apply]
  simp only [Pi.conj_apply]
  simp only [Ket.apply]
  simp only [MonoidWithZeroHom.map_ite_one_zero]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  simp

/-! ### W3. The same bra-ket in one call: name the definitions; `simp` finds R4, R6–R11 itself -/
example : 〈Ket.basis (0 : Fin 2)‖q〉 = 3 / 5 := by
  simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply, q]

/-! ### W4. A normalization sum with a `√`, step by step: R14, R15, R16, R17, R18, R19, R20, R21 -/
example : ∑ _x : Fin 3, ‖((Real.sqrt 3)⁻¹ : ℂ)‖ ^ 2 = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [norm_inv]
  simp only [Complex.norm_real]
  simp only [Real.norm_eq_abs]
  simp only [inv_pow]
  simp only [sq_abs]
  simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [mul_inv_cancel₀ (by norm_num)]

/-! ### W5. The same sum in one call -/
example : ∑ _x : Fin 3, ‖((Real.sqrt 3)⁻¹ : ℂ)‖ ^ 2 = 1 := by
  simp

end E112Guide
