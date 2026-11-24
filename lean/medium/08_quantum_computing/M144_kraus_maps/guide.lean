/- Guide for M144 (Kraus maps are trace preserving and positive).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`/`Q` stand for "the rest of your goal (or hypothesis)": the step changes only the part shown inside
`P (…)`. A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix
open scoped ComplexOrder

namespace M144Guide

/-! # Part R · Reference entries -/

/-! ## Traces of sums of products -/

/-! ### R1. `rw [D]` for a definition `D` with arguments · goal: `D a b` → its body -/
def sandwich {n : Type} [Fintype n] (A M : Matrix n n ℂ) : Matrix n n ℂ := A * M * A
example {n : Type} [Fintype n] (A M : Matrix n n ℂ) (P : Matrix n n ℂ → Prop) (h : P (A * M * A)) :
    P (sandwich A M) := by
  rw [sandwich]
  exact h

/-! ### R2. `Matrix.trace_sum` · `(∑ i ∈ s, f i).trace = ∑ i ∈ s, (f i).trace` · goal -/
example {ι n R : Type} [Fintype ι] [Fintype n] [CommRing R] (f : ι → Matrix n n R) (P : R → Prop)
    (h : P (∑ i, (f i).trace)) : P (∑ i, f i).trace := by
  rw [Matrix.trace_sum]
  exact h

/-! ### R3. `Matrix.trace_mul_cycle` · `(A * B * C).trace = (C * A * B).trace` · goal (one term) -/
example {n R : Type} [Fintype n] [CommRing R] (A B C : Matrix n n R) (P : R → Prop)
    (h : P (C * A * B).trace) : P (A * B * C).trace := by
  rw [Matrix.trace_mul_cycle]
  exact h

/-! ### R4. `simp_rw [Matrix.trace_mul_cycle (A _) M]` · goal: R3 in every term UNDER `∑ i, …`
`rw` cannot rewrite a term that mentions the bound `i`; `simp_rw` can. Pinning the first two factors
`(A _) M` makes it fire once per term instead of rotating forever. The bound name may become `x`. -/
example {ι n R : Type} [Fintype ι] [Fintype n] [CommRing R] (A C : ι → Matrix n n R) (M : Matrix n n R)
    (P : R → Prop) (h : P (∑ i, (C i * A i * M).trace)) : P (∑ i, (A i * M * C i).trace) := by
  simp_rw [Matrix.trace_mul_cycle (A _) M]
  exact h

/-! ### R5. `rw [← Matrix.trace_sum]` · goal: a sum of traces → the trace of one sum -/
example {ι n R : Type} [Fintype ι] [Fintype n] [CommRing R] (f : ι → Matrix n n R) (P : R → Prop)
    (h : P (∑ i, f i).trace) : P (∑ i, (f i).trace) := by
  rw [← Matrix.trace_sum]
  exact h

/-! ### R6. `Finset.sum_mul` · `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`; `rw [← Finset.sum_mul]` pulls
a common right factor out of a sum · goal -/
example {ι n R : Type} [Fintype ι] [Fintype n] [CommRing R] (f : ι → Matrix n n R) (M : Matrix n n R)
    (P : Matrix n n R → Prop) (h : P ((∑ i, f i) * M)) : P (∑ i, f i * M) := by
  rw [← Finset.sum_mul]
  exact h

/-! ### R7. `Matrix.one_mul` · `1 * M = M` · goal -/
example {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (M : Matrix n n R)
    (P : Matrix n n R → Prop) (h : P M) : P (1 * M) := by
  rw [Matrix.one_mul]
  exact h

/-! ## Positive semidefinite matrices as quadratic forms -/

/-! ### R8. `rw [Matrix.posSemidef_iff_dotProduct_mulVec] at *` · context AND goal
`M.PosSemidef ↔ M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x`, rewritten in every hypothesis and the goal. -/
example {n : Type} [Fintype n] (A M : Matrix n n ℂ) (hA : A.PosSemidef)
    (h : (A.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ A *ᵥ x) → M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x) :
    M.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at *
  exact h hA

/-! ### R9. `refine ⟨e, fun x => ?_⟩` · goal `A ∧ ∀ x, Q x` → context gains `x`, goal `Q x` -/
example {α : Type} (A : Prop) (Q : α → Prop) (a : A) (hQ : ∀ x, Q x) : A ∧ ∀ x, Q x := by
  refine ⟨a, fun x => ?_⟩
  exact hQ x

/-! ### R10. `Matrix.isHermitian_mul_mul_conjTranspose B hA` · `A.IsHermitian → (B * A * Bᴴ).IsHermitian`
· context gains the fact (or use the term directly as the first component in R9) -/
example {n : Type} [Fintype n] (A B : Matrix n n ℂ) (hA : A.IsHermitian) (G : Prop)
    (h : (B * A * Bᴴ).IsHermitian → G) : G := by
  have hB := Matrix.isHermitian_mul_mul_conjTranspose B hA
  exact h hB

/-! ### R11. `have := h.2 v` · `h : A ∧ ∀ x, Q x`; `h.2` is the `∀` half, applied to `v` · context
gains `this : Q v` (`h.1 : A` is the other half) -/
example {α : Type} (A : Prop) (Q : α → Prop) (h : A ∧ ∀ x, Q x) (v : α) : Q v := by
  have := h.2 v
  exact this

/-! ## Moving matrices across the dot product -/

/-! ### R12. `Matrix.star_mulVec` · `star (M *ᵥ v) = star v ᵥ* Mᴴ`; `rw [...] at h` · context -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) (Q : (n → ℂ) → Prop)
    (h : Q (star (M *ᵥ v))) : Q (star v ᵥ* Mᴴ) := by
  rw [Matrix.star_mulVec] at h
  exact h

/-! ### R13. `Matrix.conjTranspose_conjTranspose` · `Mᴴᴴ = M`; `rw [...] at h` · context -/
example {n : Type} (M : Matrix n n ℂ) (Q : Matrix n n ℂ → Prop) (h : Q Mᴴᴴ) : Q M := by
  rw [Matrix.conjTranspose_conjTranspose] at h
  exact h

/-! ### R14. `Matrix.dotProduct_mulVec` · `v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w`; `rw [← …] at h` moves `A` from
the left vector onto the right one · context -/
example {n : Type} [Fintype n] (A : Matrix n n ℂ) (v w : n → ℂ) (Q : ℂ → Prop)
    (h : Q (v ᵥ* A ⬝ᵥ w)) : Q (v ⬝ᵥ A *ᵥ w) := by
  rw [← Matrix.dotProduct_mulVec] at h
  exact h

/-! ### R15. `Matrix.mulVec_mulVec` · `M *ᵥ N *ᵥ v = (M * N) *ᵥ v`; `rw [← …]` splits a product acting
on a vector into two actions, peeling off the RIGHTMOST factor · goal -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (v : n → ℂ) (Q : (n → ℂ) → Prop)
    (h : Q (M *ᵥ N *ᵥ v)) : Q ((M * N) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec]
  exact h

/-! ### R16. `rwa [e]` · `rw [e]`, then close the goal with a hypothesis that now matches it -/
example {α : Type} (a b : α) (P : α → Prop) (e : a = b) (h : P b) : P a := by
  rwa [e]

/-! ## Sums of PSD matrices -/

/-! ### R17. `apply Matrix.posSemidef_sum` · goal `(∑ i, x i).PosSemidef` → `∀ i ∈ Finset.univ, …`;
then `intro i _` · context gains `i` and `i ∈ Finset.univ` -/
example {ι n : Type} [Fintype ι] [Fintype n] (x : ι → Matrix n n ℂ) (h : ∀ i, (x i).PosSemidef) :
    (∑ i, x i).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact h i

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Push the trace in, rotate every term, fold back: R2 → R4 → R5
`rw [Matrix.trace_sum]` rewrites only the left side: the right side's sum has a different `f`. -/
example {ι n : Type} [Fintype ι] [Fintype n] (A C : ι → Matrix n n ℂ) (M : Matrix n n ℂ) :
    (∑ i, A i * M * C i).trace = (∑ i, C i * A i * M).trace := by
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (A _) M]
  rw [← Matrix.trace_sum]

/-! ### W2. Moving a matrix out of a `star`ed vector and across `⬝ᵥ`: R12 → R14 -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v w : n → ℂ) :
    star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w := by
  rw [Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec]

end M144Guide
