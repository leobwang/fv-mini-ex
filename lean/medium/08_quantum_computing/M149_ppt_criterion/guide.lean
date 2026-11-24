/- Guide for M149 (The PPT (Peres–Horodecki) criterion).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the full transpose, √3, |00⟩).
Assumed: Lean basics.
-/
import Mathlib

open Matrix
open scoped Kronecker ComplexOrder

namespace M149Guide

/-! # Part R · Reference entries -/

/-! ## Matrices indexed by pairs: entries of `of`, `⊗ₖ`, `ᵀ`, sums and scalings -/

/-! ### R1. `ext ⟨a, b⟩ ⟨c, e⟩` (lemma `Matrix.ext`) · goal `M = N` → one entry, indices split
Rows and columns of `M : Matrix (α × β) (α × β) γ` are pairs; the patterns name both components. -/
example {α β γ : Type} (M N : Matrix (α × β) (α × β) γ)
    (h : ∀ a b c e, M (a, b) (c, e) = N (a, b) (c, e)) : M = N := by
  ext ⟨a, b⟩ ⟨c, e⟩
  exact h a b c e

/-! ### R2. `Matrix.of_apply` · `of f i j = f i j` · goal: entry of a matrix built by `Matrix.of`
On pair indices the projections `(a, b).1` are left behind; `simp` reduces them to `a`. -/
example {m n α : Type} (f : m → n → α) (i : m) (j : n) (P : α → Prop) (h : P (f i j)) :
    P (Matrix.of f i j) := by
  rw [Matrix.of_apply]
  exact h

example {α β γ : Type} (g : α × β → α × β → γ) (a c : α) (b e : β) (P : γ → Prop)
    (h : P (g (c, b) (a, e))) : P (Matrix.of (fun p q => g (q.1, p.2) (p.1, q.2)) (a, b) (c, e)) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R3. `Matrix.kronecker_apply` · `(A ⊗ₖ B) (a, b) (c, e) = A a c * B b e` · goal
The infoview prints `A ⊗ₖ B` as `kroneckerMap (fun x1 x2 => x1 * x2) A B`. -/
example {α β γ : Type} [Mul γ] (A : Matrix α α γ) (B : Matrix β β γ) (a c : α) (b e : β)
    (P : γ → Prop) (h : P (A a c * B b e)) : P ((A ⊗ₖ B) (a, b) (c, e)) := by
  rw [Matrix.kronecker_apply]
  exact h

/-! ### R4. `Matrix.transpose_apply` · `Mᵀ i j = M j i` · goal -/
example {n α : Type} (M : Matrix n n α) (i j : n) (P : α → Prop) (h : P (M j i)) : P (Mᵀ i j) := by
  rw [Matrix.transpose_apply]
  exact h

/-! ### R5. `Matrix.sum_apply` · `(∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j` · goal: entry of a sum -/
example {ι n : Type} [Fintype ι] (X : ι → Matrix n n ℂ) (i j : n) (P : ℂ → Prop)
    (h : P (∑ k, X k i j)) : P ((∑ k, X k) i j) := by
  rw [Matrix.sum_apply]
  exact h

/-! ### R6. `Matrix.smul_apply`, then `Complex.real_smul` · goal: entry of `r • M` (`r : ℝ`) → `↑r * M i j` -/
example {n : Type} (r : ℝ) (M : Matrix n n ℂ) (i j : n) (P : ℂ → Prop) (h : P (↑r * M i j)) :
    P ((r • M) i j) := by
  rw [Matrix.smul_apply]
  rw [Complex.real_smul]
  exact h

/-! ## Building positive semidefinite matrices -/

/-! ### R7. `Matrix.posSemidef_sum` · goal list: PSD of a sum → PSD of each term
`refine Matrix.posSemidef_sum _ fun k _ => ?_` leaves one goal with `k` and `k ∈ Finset.univ` in context. -/
example {ι n : Type} [Fintype ι] (X : ι → Matrix n n ℂ) (h : ∀ k, (X k).PosSemidef) :
    (∑ k, X k).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  exact h k

/-! ### R8. `Matrix.PosSemidef.smul` · `X.PosSemidef → 0 ≤ r → (r • X).PosSemidef` · goal -/
example {n : Type} (r : ℝ) (X : Matrix n n ℂ) (hr : 0 ≤ r) (hX : X.PosSemidef) :
    (r • X).PosSemidef := by
  refine Matrix.PosSemidef.smul ?_ hr
  exact hX

/-! ### R9. `Matrix.PosSemidef.kronecker` · `A.PosSemidef → B.PosSemidef → (A ⊗ₖ B).PosSemidef` · goal list -/
example {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊗ₖ B).PosSemidef := by
  refine Matrix.PosSemidef.kronecker ?_ ?_
  exacts [hA, hB]

/-! ### R10. `Matrix.PosSemidef.transpose` · `M.PosSemidef → Mᵀ.PosSemidef` · goal -/
example {n : Type} (M : Matrix n n ℂ) (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  refine Matrix.PosSemidef.transpose ?_
  exact hM

/-! ## Refuting positivity with one test vector -/

/-! ### R11. `intro h` on `¬ A` · `¬ A` is `A → False`: context gains `h : A`, goal becomes `False` -/
example (A : Prop) (h0 : A → False) : ¬ A := by
  intro h
  exact h0 h

/-! ### R12. `set v : τ := e` · context gains the local definition `v : τ := e`; `e` in the goal → `v` -/
example (f : (Fin 2 → ℂ) → Prop) (h : ∀ w, f w) : f (fun i => if i = 0 then 1 else 0) := by
  set v : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0
  exact h v

/-! ### R13. `Matrix.PosSemidef.dotProduct_mulVec_nonneg` · `M.PosSemidef → ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x`
`have h1 := hM.dotProduct_mulVec_nonneg v` adds the inequality for your test vector `v` · context -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef) (v : n → ℂ)
    (h : 0 ≤ star v ⬝ᵥ M *ᵥ v → False) : False := by
  have h1 := hM.dotProduct_mulVec_nonneg v
  exact h h1

/-! ### R14. `Complex.ofReal_pow` · `↑(x ^ n) = ↑x ^ n`; right to left moves `^` inside the cast -/
example (x : ℝ) (n : ℕ) (P : ℂ → Prop) (h : P ↑(x ^ n)) : P (↑x ^ n) := by
  rw [← Complex.ofReal_pow]
  exact h

/-! ### R15. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` · goal -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ### R16. `dotProduct` (unfold) · `v ⬝ᵥ w` → `∑ i, v i * w i` · goal -/
example {n : Type} [Fintype n] (v w : n → ℂ) (P : ℂ → Prop) (h : P (∑ i, v i * w i)) :
    P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R17. `Matrix.mulVec` (unfold) · `(M *ᵥ v) i` → `(fun j => M i j) ⬝ᵥ v` · goal -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) (i : n) (P : ℂ → Prop)
    (h : P (∑ j, M i j * v j)) : P ((M *ᵥ v) i) := by
  simp only [Matrix.mulVec]
  simp only [dotProduct]
  exact h

/-! ### R18. `Matrix.vecMulVec` (unfold) · `vecMulVec w u = of fun x y => w x * u y` · goal
Then R2 gives the entry `w i * u j`. -/
example {n : Type} (w u : n → ℂ) (i j : n) (P : ℂ → Prop) (h : P (w i * u j)) :
    P (vecMulVec w u i j) := by
  simp only [Matrix.vecMulVec]
  simp only [Matrix.of_apply]
  exact h

/-! ### R19. `Pi.star_apply`, then `Complex.star_def` · goal: `star v i` → `(starRingEnd ℂ) (v i)`
`star` of a vector is entrywise; on `ℂ` it is the conjugate, printed `(starRingEnd ℂ) z`. -/
example {n : Type} (v : n → ℂ) (i : n) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) (v i))) :
    P (star v i) := by
  rw [Pi.star_apply]
  rw [Complex.star_def]
  exact h

/-! ### R20. `Fintype.sum_prod_type` · `∑ x, f x = ∑ a, ∑ b, f (a, b)` · goal: a sum over pairs → a double sum -/
example {α β γ : Type} [Fintype α] [Fintype β] [AddCommMonoid γ] (f : α × β → γ) (P : γ → Prop)
    (h : P (∑ a, ∑ b, f (a, b))) : P (∑ x, f x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R21. `Fin.sum_univ_two` · `∑ i : Fin 2, f i = f 0 + f 1` · goal -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R22. `field_simp` · goal: clears `⁻¹` and `/` by multiplying out (needs `a ≠ 0`)
It finds `a ≠ 0` in the context, or proves it itself for casts such as `↑√3`. -/
example (a : ℂ) (ha : a ≠ 0) (h : 3 = a ^ 2) : a⁻¹ * a⁻¹ = 1 / 3 := by
  field_simp
  exact h

/-! ### R23. `linear_combination e` · closes `L = R` when `L - R - (e.lhs - e.rhs) = 0` by `ring`
Here `L - R - (x ^ 2 - 3) = (x ^ 2 + 1 - 4) - (x ^ 2 - 3) = 0`. Use `-e`, `2 * e`, … to scale. -/
example (x : ℂ) (h : x ^ 2 = 3) : x ^ 2 + 1 = 4 := by linear_combination h

/-! ### R24. `rw [hv] at h1` · context: rewrites inside the hypothesis `h1` instead of the goal -/
example (c d : ℂ) (h1 : 0 ≤ c) (hv : c = d) (h : 0 ≤ d → False) : False := by
  rw [hv] at h1
  exact h h1

/-! ### R25. `Complex.nonneg_iff` · `0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im` · context (with `at`)
On `ℂ`, `≤` (from `ComplexOrder`) means: real parts ordered, imaginary parts equal. -/
example (h1 : (0 : ℂ) ≤ -1) (h : 0 ≤ (-1 : ℂ).re ∧ 0 = (-1 : ℂ).im → False) : False := by
  rw [Complex.nonneg_iff] at h1
  exact h h1

/-! ### R26. `norm_num at h1` · goal list: if `h1` simplifies to `False`, the goal is closed -/
example (h1 : 0 ≤ (-1 : ℂ).re ∧ 0 = (-1 : ℂ).im) : False := by
  norm_num at h1

/-! ## Combining the theorems -/

/-! ### R27. `rintro ⟨x, ha, hb⟩` on `¬ ∃ x, A x ∧ B x` · context gains the witness and both facts; goal `False` -/
example {α : Type} (A B : α → Prop) (hn : ∀ x, A x → B x → False) : ¬ ∃ x, A x ∧ B x := by
  rintro ⟨x, ha, hb⟩
  exact hn x ha hb

/-! ### R28. `h ▸ e` · from `h : a = b` and `e : P b`, a proof of `P a` (rewrites `e`'s type with `h`) -/
example {α : Type} (P : α → Prop) (a b : α) (h : a = b) (e : P b) : P a := by
  exact h ▸ e

/-! ### R29. `exact hn e` · closes `False` from `hn : ¬ A` and `e : A` (`¬ A` is a function `A → False`) -/
example (A : Prop) (hn : ¬ A) (e : A) : False := by
  exact hn e

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Transpose of a Kronecker product, entry by entry: R1, then R4 and R3 -/
example {α β : Type} (A : Matrix α α ℂ) (B : Matrix β β ℂ) : (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [Matrix.transpose_apply, Matrix.kronecker_apply]

/-! ### W2. The transpose is linear: R1, then `simp` with R5 (it applies R4, R6 by itself) -/
example {ι n : Type} [Fintype ι] (p : ι → ℝ) (X : ι → Matrix n n ℂ) :
    (∑ k, p k • X k)ᵀ = ∑ k, p k • (X k)ᵀ := by
  ext a b
  simp [Matrix.sum_apply]

/-! ### W3. A mixture `∑ k, p k • ((A k)ᵀ ⊗ₖ B)` (first factor transposed, one fixed `B`) is PSD:
R7, then R8, R9, R10 as one term -/
example {ι m n : Type} [Fintype ι] [Fintype m] [Fintype n] (p : ι → ℝ) (A : ι → Matrix m m ℂ)
    (B : Matrix n n ℂ) (hp : ∀ k, 0 ≤ p k) (hA : ∀ k, (A k).PosSemidef)
    (hB : B.PosSemidef) : (∑ k, p k • ((A k)ᵀ ⊗ₖ B)).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  exact ((hA k).transpose.kronecker hB).smul (hp k)

/-! ### W4. A quadratic form on `Fin 2 × Fin 2`: the √3 fact (R14, R15), then `simp` with R16–R21,
then R22, R23. `w = |00⟩/√3` and the test vector `u = |00⟩ + |11⟩`. -/
noncomputable def w : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 0) then ((Real.sqrt 3)⁻¹ : ℂ) else 0
def u : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num)]
  simp

theorem quad_w : star u ⬝ᵥ (-(vecMulVec w (star w)) *ᵥ u) = -1 / 3 := by
  simp [u, w, dotProduct, Matrix.mulVec, Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
  field_simp
  linear_combination sqrt3_sq

/-! ### W5. So `-(|w⟩⟨w|)` is not PSD: R11, R13, then R24, R25, R26 -/
example : ¬ (-(vecMulVec w (star w))).PosSemidef := by
  intro h
  have h1 := h.dotProduct_mulVec_nonneg u
  rw [quad_w] at h1
  rw [Complex.nonneg_iff] at h1
  norm_num at h1

end M149Guide
