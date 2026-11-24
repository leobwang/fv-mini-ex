/- Guide for M147 (Trace distance is a unitarily invariant metric).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (sums of three matrices,
conjugated sums).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Mixed.TraceDistance
import QuantumInfo.Operators.Unitary

open Matrix

namespace M147Guide

/-! # Part R · Reference entries -/

/-! ## Iff, states, and the trace norm -/

/-! ### R1. `constructor` on `↔` · goal list: `A ↔ B` → `A → B` (case `mp`), `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exacts [hab, hba]

/-! ### R2. `apply MState.ext_m` · goal: equality of states → equality of their density matrices
`MState d` is a density matrix on the finite index type `d` (a positive semidefinite Hermitian
matrix of trace 1); `ρ.m : Matrix d d ℂ` is its matrix. `MState.ext_m : ρ₁.m = ρ₂.m → ρ₁ = ρ₂`. -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ₁ ρ₂ : MState d) (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  apply MState.ext_m
  exact h

/-! ### R3. `sub_eq_zero` · `a - b = 0 ↔ a = b`; right to left: `rw [← sub_eq_zero]` · goal -/
example {α : Type} [AddGroup α] (a b : α) (h : a - b = 0) : a = b := by
  rw [← sub_eq_zero]
  exact h

/-! ### R4. `Matrix.traceNorm_zero_iff` · `A.traceNorm = 0 ↔ A = 0`; right to left · goal
`A.traceNorm` is the trace norm `‖A‖₁ = Tr √(Aᴴ A)`, the sum of the singular values of `A`. -/
example {d : Type} [Fintype d] (A : Matrix d d ℂ) (h : A.traceNorm = 0) : A = 0 := by
  rw [← Matrix.traceNorm_zero_iff]
  exact h

/-! ### R5. `unfold TrDistance at h` · context: `h` gets the definition
`TrDistance ρ σ := 1 / 2 * (ρ.m - σ.m).traceNorm` (a real number). -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ₁ ρ₂ : MState d) (P : ℝ → Prop)
    (h : P (TrDistance ρ₁ ρ₂)) : P (1 / 2 * (ρ₁.m - ρ₂.m).traceNorm) := by
  unfold TrDistance at h
  exact h

/-! ### R6. `Matrix.traceNorm_nonneg` · `0 ≤ A.traceNorm` · context gains the fact -/
example {d : Type} [Fintype d] (A : Matrix d d ℂ) (G : Prop) (g : 0 ≤ A.traceNorm → G) : G := by
  have := Matrix.traceNorm_nonneg A
  exact g this

/-! ### R7. `linarith [t]` · closes a linear (in)equality over `ℝ` from the hypotheses plus the extra
facts `t`. Without `[Matrix.traceNorm_nonneg A]` this one fails: `linarith` knows nothing about
`traceNorm`, it treats `A.traceNorm` as an unknown real number. -/
example {d : Type} [Fintype d] (A : Matrix d d ℂ) (h : 1 / 2 * A.traceNorm ≤ 0) :
    A.traceNorm = 0 := by
  linarith [Matrix.traceNorm_nonneg A]

/-! ### R8. `rintro rfl` · goal `a = b → G`: introduce the equation and substitute it; context loses `b` -/
example {α : Type} (P : α → α → Prop) (h : ∀ x, P x x) (a b : α) : a = b → P a b := by
  rintro rfl
  exact h a

/-! ### R9. `simp` on `(A - A).traceNorm` · goal: → `0` (`sub_self`, then `Matrix.traceNorm_zero`) -/
example {d : Type} [Fintype d] (A : Matrix d d ℂ) (P : ℝ → Prop) (h : P 0) :
    P (A - A).traceNorm := by
  simp
  exact h

/-! ## The triangle inequality -/

/-! ### R10. `Matrix.traceNorm_add_le` · `(A + B).traceNorm ≤ A.traceNorm + B.traceNorm` · context -/
example {d : Type} [Fintype d] (A B : Matrix d d ℂ) (G : Prop)
    (g : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm → G) : G := by
  have := Matrix.traceNorm_add_le A B
  exact g this

/-! ### R11. `rw [sub_add_sub_cancel] at this` · `a - b + (b - c) = a - c` · context -/
example {α : Type} [AddGroup α] (a b c : α) (Q : α → Prop) (this : Q (a - b + (b - c))) :
    Q (a - c) := by
  rw [sub_add_sub_cancel] at this
  exact this

/-! ### R12. `unfold TrDistance` · goal: every `TrDistance x y` → `1 / 2 * (x.m - y.m).traceNorm` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ₁ ρ₂ : MState d) (P : ℝ → Prop)
    (h : P (1 / 2 * (ρ₁.m - ρ₂.m).traceNorm)) : P (TrDistance ρ₁ ρ₂) := by
  unfold TrDistance
  exact h

/-! ## Unitary conjugation -/

/-! ### R13. `simp only [MState.uConj]` · goal: `ρ.uConj U` → the state it is built as
`U : 𝐔[d]` is a unitary (an element of `Matrix.unitaryGroup d ℂ`); `↑U : Matrix d d ℂ` its matrix.
`ρ.uConj U` is the state `U ρ U†`; its field `M` is `HermitianMat.conj ↑U ↑ρ`. -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (U : 𝐔[d]) (P : Matrix d d ℂ → Prop)
    (h : P ((U : Matrix d d ℂ) * ρ.m * (U : Matrix d d ℂ)ᴴ)) : P (ρ.uConj U).m := by
  simp only [MState.uConj]
  exact h

/-! ### R14. `simp only [MState.m]` · goal: `x.m` → `↑x.M`, the matrix of the Hermitian matrix `x.M`
On a plain state `ρ`, `ρ.m` becomes `↑↑ρ` (state → Hermitian matrix → matrix). -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (P : Matrix d d ℂ → Prop)
    (h : P ρ.M.mat) : P ρ.m := by
  simp only [MState.m]
  exact h

/-! ### R15. `HermitianMat.conj_apply_mat` · `(A.conj B).mat = B * A.mat * Bᴴ` · goal -/
example {d : Type} [Fintype d] (A : HermitianMat d ℂ) (B : Matrix d d ℂ) (P : Matrix d d ℂ → Prop)
    (h : P (B * A.mat * Bᴴ)) : P (A.conj B).mat := by
  simp only [HermitianMat.conj_apply_mat]
  exact h

/-! ### R16. `Matrix.sub_mul` · `(M - M') * N = M * N - M' * N`; right to left factors `N` out -/
example {d : Type} [Fintype d] (M M' N : Matrix d d ℂ) (P : Matrix d d ℂ → Prop)
    (h : P ((M - M') * N)) : P (M * N - M' * N) := by
  rw [← Matrix.sub_mul]
  exact h

/-! ### R17. `Matrix.mul_sub` · `M * (N - N') = M * N - M * N'`; right to left factors `M` out -/
example {d : Type} [Fintype d] (M N N' : Matrix d d ℂ) (P : Matrix d d ℂ → Prop)
    (h : P (M * (N - N'))) : P (M * N - M * N') := by
  rw [← Matrix.mul_sub]
  exact h

/-! ### R18. `Matrix.traceNorm_unitary_conj` · `(↑U * A * (↑U)ᴴ).traceNorm = A.traceNorm` · context
Its `U` lives in the lemma's copy of the unitary group, built from other (but equal) instances for
`DecidableEq d` and the ring structure of `ℂ`. So `rw` cannot use it on your `U : 𝐔[d]`: rebuild
`U` as `⟨U.val, by convert U.2 <;> rfl⟩` (R20 explains the `convert`). -/
example {d : Type} [Fintype d] [DecidableEq d] (V : 𝐔[d]) (A : Matrix d d ℂ) (G : Prop) (g : G) :
    G := by
  have := Matrix.traceNorm_unitary_conj (A := A) (U := ⟨V.val, by convert V.2 <;> rfl⟩)
  exact g

/-! ### R19. `simpa using this` · closes the goal: simplifies `this` and the goal, then matches them
Here it erases the wrapper: `↑⟨a, ha⟩` (the value of a subtype element built from `a`) is `a`. -/
example {α : Type} (p : α → Prop) (a : α) (ha : p a) (Q : α → Prop) (this : Q a) :
    Q (⟨a, ha⟩ : Subtype p).val := by
  simpa using this

/-! ### R20. `convert h` · goal list: closes the goal with `h` up to the parts that differ, and
leaves one equation per difference. In R18 the differences are instance equations such as
`Complex.instRCLike.toCommRing = Complex.commRing` (two routes to the same ring `ℂ`): `rfl`. -/
example (P : ℕ → Prop) (a b : ℕ) (hab : a = b) (h : P a) : P b := by
  convert h
  exact hab.symm

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Three matrices: R10 twice, then R7 -/
example {d : Type} [Fintype d] (A B C : Matrix d d ℂ) :
    (A + B + C).traceNorm ≤ A.traceNorm + B.traceNorm + C.traceNorm := by
  have h1 := Matrix.traceNorm_add_le (A + B) C
  have h2 := Matrix.traceNorm_add_le A B
  linarith

/-! ### W2. A conjugated sum: factor with `Matrix.add_mul`, `Matrix.mul_add` (the `+` cousins of R16,
R17), then the R18 → R19 idiom as a `have`, then R10 -/
example {d : Type} [Fintype d] [DecidableEq d] (V : 𝐔[d]) (A B : Matrix d d ℂ) :
    ((V : Matrix d d ℂ) * A * (V : Matrix d d ℂ)ᴴ + (V : Matrix d d ℂ) * B * (V : Matrix d d ℂ)ᴴ).traceNorm
      ≤ A.traceNorm + B.traceNorm := by
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  have key := Matrix.traceNorm_unitary_conj (A := A + B) (U := ⟨V.val, by convert V.2 <;> rfl⟩)
  simp only at key
  rw [key]
  exact Matrix.traceNorm_add_le A B

end M147Guide
