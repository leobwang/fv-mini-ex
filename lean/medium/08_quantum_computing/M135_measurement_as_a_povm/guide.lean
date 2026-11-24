/- Guide for M135 (Measurement as a POVM).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a constant diagonal, a general
diagonal-times-matrix trace, an arbitrary POVM).
Assumed: Lean basics. `ι` is any finite index type with decidable equality (`Fin 2`, `Fin 2 × Fin 2`).
-/
import QuantumInfo.Measurements.POVM

open scoped Matrix ComplexOrder

namespace M135Guide

/-! # Part R · Reference entries -/

/-! ## `0 ≤ A` for a Hermitian matrix -/

/-! ### R1. `HermitianMat.zero_le_iff` · goal: `0 ≤ A` → `(↑A).PosSemidef` -/
example {ι : Type} [Fintype ι] (A : HermitianMat ι ℂ) (h : (A.mat).PosSemidef) : 0 ≤ A := by
  rw [HermitianMat.zero_le_iff]
  exact h

/-! ### R2. `rw [D]` · goal: a defined name applied to arguments → its body
`Dg c` is the constant diagonal `c · 1`, used only in this guide. -/
noncomputable def Dg {ι : Type} [DecidableEq ι] (c : ℝ) : HermitianMat ι ℂ :=
  HermitianMat.diagonal ℂ (fun _ => c)

example {ι : Type} [DecidableEq ι] (c : ℝ) (P : HermitianMat ι ℂ → Prop)
    (h : P (HermitianMat.diagonal ℂ fun _ => c)) : P (Dg c) := by
  rw [Dg]
  exact h

/-! ### R3. `HermitianMat.diagonal_mat` · goal: `↑(HermitianMat.diagonal ℂ f)` → `Matrix.diagonal …`
`↑(f x)` on the right is the real number `f x` cast into `ℂ` (`RCLike.ofReal`). -/
example {ι : Type} [DecidableEq ι] (f : ι → ℝ) (P : Matrix ι ι ℂ → Prop)
    (h : P (Matrix.diagonal fun x => (f x : ℂ))) : P (HermitianMat.diagonal ℂ f).mat := by
  rw [HermitianMat.diagonal_mat]
  exact h

/-! ### R4. `Matrix.posSemidef_diagonal_iff` · goal: `(Matrix.diagonal v).PosSemidef` → `∀ i, 0 ≤ v i` -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (h : ∀ i, 0 ≤ v i) :
    (Matrix.diagonal v).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  exact h

/-! ### R5. `intro j` · goal `∀ i, Q i` → context gains `j`, goal `Q j` -/
example {ι : Type} (Q : ι → Prop) (h : ∀ i, Q i) : ∀ i, Q i := by
  intro j
  exact h j

/-! ### R6. `split_ifs` · goal with `if p then a else b` → two goals, one per branch
Each new goal gets the branch condition as an unnamed hypothesis `h✝`; `split_ifs with hp` names it. -/
example {α : Type} (p : Prop) [Decidable p] (a b : α) (P : α → Prop) (ha : P a) (hb : P b) :
    P (if p then a else b) := by
  split_ifs
  exacts [ha, hb]

/-! ### R7. `RCLike.ofReal_nonneg` · `0 ≤ ↑x ↔ 0 ≤ x` · goal: a complex inequality → a real one
With `open scoped ComplexOrder`, `z ≤ w` on `ℂ` means `z.re ≤ w.re ∧ z.im = w.im`. -/
example (x : ℝ) (hx : 0 ≤ x) : (0 : ℂ) ≤ RCLike.ofReal x := by
  rw [RCLike.ofReal_nonneg]
  exact hx

/-- `simp` closes the numeral cases by itself (it also knows `↑1 = 1`, `↑0 = 0`). -/
example : (0 : ℂ) ≤ RCLike.ofReal 1 := by
  simp

/-! ## Sums of Hermitian matrices, entry by entry -/

/-! ### R8. `ext1` (lemma `HermitianMat.ext`) · goal `A = B` → `↑A = ↑B` (equal underlying matrices) -/
example {ι : Type} (A B : HermitianMat ι ℂ) (h : A.mat = B.mat) : A = B := by
  ext1
  exact h

/-! ### R9. `HermitianMat.mat_finset_sum` · `↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)` · goal: `↑` moves inside `∑` -/
example {ι κ : Type} [Fintype κ] (f : κ → HermitianMat ι ℂ) (P : Matrix ι ι ℂ → Prop)
    (h : P (∑ k, (f k).mat)) : P (∑ k, f k).mat := by
  rw [HermitianMat.mat_finset_sum]
  exact h

/-! ### R10. `ext a b` (lemma `Matrix.ext`) · goal `M = N` → context gains `a b : ι`, goal one entry -/
example {ι : Type} (M N : Matrix ι ι ℂ) (h : ∀ a b, M a b = N a b) : M = N := by
  ext a b
  exact h a b

/-! ### R11. `Matrix.sum_apply` · `(∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j` · goal: entry of a sum → sum of entries -/
example {ι κ : Type} [Fintype κ] (g : κ → Matrix ι ι ℂ) (a b : ι) (P : ℂ → Prop)
    (h : P (∑ k, g k a b)) : P ((∑ k, g k) a b) := by
  rw [Matrix.sum_apply]
  exact h

/-! ### R12. `Matrix.diagonal_apply` · `diagonal v i j = if i = j then v i else 0` · goal -/
example {ι : Type} [DecidableEq ι] (v : ι → ℂ) (a b : ι) (P : ℂ → Prop)
    (h : P (if a = b then v a else 0)) : P (Matrix.diagonal v a b) := by
  rw [Matrix.diagonal_apply]
  exact h

/-! ### R13. `HermitianMat.mat_one`, then `Matrix.one_apply` · goal: entry of the identity → an `if` -/
example {ι : Type} [DecidableEq ι] (a b : ι) (P : ℂ → Prop) (h : P (if a = b then 1 else 0)) :
    P ((1 : HermitianMat ι ℂ).mat a b) := by
  rw [HermitianMat.mat_one]
  rw [Matrix.one_apply]
  exact h

/-! ### R14. `MonoidWithZeroHom.map_ite_one_zero` · goal: `↑(if p then 1 else 0)` → `if p then 1 else 0`
The cast `ℝ → ℂ` is a ring map, so it can be pushed into both branches of a `1`/`0` `if`. -/
example (p : Prop) [Decidable p] (P : ℂ → Prop) (h : P (if p then 1 else 0)) :
    P (RCLike.ofReal (if p then 1 else 0)) := by
  simp only [MonoidWithZeroHom.map_ite_one_zero]
  exact h

/-! ### R15. `Finset.sum_ite_irrel` · goal: an `if` whose condition ignores the summation variable moves out of `∑` -/
example {κ : Type} [Fintype κ] (p : Prop) [Decidable p] (f g : κ → ℂ) (P : ℂ → Prop)
    (h : P (if p then ∑ k, f k else ∑ k, g k)) : P (∑ k, if p then f k else g k) := by
  rw [Finset.sum_ite_irrel]
  exact h

/-! ### R16. `Finset.sum_ite_eq` · `(∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0`
A Kronecker delta `δ_{a x}` under `∑ x` picks out the single term `x = a`. -/
example {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) (u : κ → ℂ) (P : ℂ → Prop)
    (h : P (if a ∈ Finset.univ then u a else 0)) : P (∑ x, if a = x then u x else 0) := by
  rw [Finset.sum_ite_eq]
  exact h

/-! ### R17. `Finset.mem_univ`, `↓reduceIte` · goal: `if a ∈ Finset.univ then u else w` → `u` -/
example {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) (u w : ℂ) (P : ℂ → Prop) (h : P u) :
    P (if a ∈ Finset.univ then u else w) := by
  simp only [Finset.mem_univ, ↓reduceIte]
  exact h

/-! ### R18. `Finset.sum_const_zero` · goal: `∑ x ∈ s, 0` → `0` -/
example {κ : Type} [Fintype κ] (P : ℂ → Prop) (h : P 0) : P (∑ _x : κ, (0 : ℂ)) := by
  rw [Finset.sum_const_zero]
  exact h

/-! ## The probability of an outcome -/

/-! ### R19. `simp only [POVM.measure]` · goal: `Λ.measure ρ x` → a distribution built from `inner ℝ (Λ.mats x) ↑ρ` -/
example {X ι : Type} [Fintype X] [Fintype ι] [DecidableEq ι] (Λ : POVM X ι) (ρ : MState ι) (x : X)
    (P : ℝ → Prop) (h : P (inner ℝ (Λ.mats x) ρ.M)) : P (Λ.measure ρ x) := by
  simp only [POVM.measure]
  simp only [ProbDistribution.mk', ProbDistribution.funlike_apply]
  exact h

/-! ### R20. `simp only [ProbDistribution.mk']` · goal: `ProbDistribution.mk' f ⋯ ⋯` → the anonymous structure `⟨…, ⋯⟩` -/
example {X : Type} [Fintype X] (f : X → ℝ) (h0 : ∀ x, 0 ≤ f x) (h1 : ∑ x, f x = 1) (x : X)
    (P : ℝ → Prop) (h : P (f x)) : P (ProbDistribution.mk' f h0 h1 x) := by
  simp only [ProbDistribution.mk']
  simp only [ProbDistribution.funlike_apply]
  exact h

/-! ### R21. `ProbDistribution.funlike_apply` · `⟨d, h⟩ x = d x` · goal: evaluate the distribution at `x`
`simp` also strips the `Prob` wrapper: `↑⟨r, ⋯⟩` becomes `r`. -/
example {X : Type} [Fintype X] (d : X → Prob) (hd : ∑ x, (d x : ℝ) = 1) (x : X) (P : ℝ → Prop)
    (h : P (d x)) : P (DFunLike.coe (F := ProbDistribution X) ⟨d, hd⟩ x) := by
  simp only [ProbDistribution.funlike_apply]
  exact h

/-! ### R22. `HermitianMat.inner_eq_re_trace` · `inner ℝ A B = RCLike.re (↑A * ↑B).trace` · goal -/
example {ι : Type} [Fintype ι] (A B : HermitianMat ι ℂ) (P : ℝ → Prop)
    (h : P (RCLike.re (A.mat * B.mat).trace)) : P (inner ℝ A B) := by
  rw [HermitianMat.inner_eq_re_trace]
  exact h

/-! ### R23. `Matrix.trace`, `Matrix.diag_apply` · goal: `M.trace` → `∑ i, M i i` -/
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (P : ℂ → Prop) (h : P (∑ i, M i i)) :
    P M.trace := by
  simp only [Matrix.trace]
  simp only [Matrix.diag_apply]
  exact h

/-! ### R24. `Matrix.diagonal_mul` · `(diagonal v * M) i j = v i * M i j` · goal: row `i` scaled by `v i` -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (M : Matrix ι ι ℂ) (i j : ι)
    (P : ℂ → Prop) (h : P (v i * M i j)) : P ((Matrix.diagonal v * M) i j) := by
  rw [Matrix.diagonal_mul]
  exact h

/-! ### R25. `MState.mat_M` · `↑↑ρ = ρ.m` · goal: the matrix of the state, two casts → one name -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : MState ι) (P : Matrix ι ι ℂ → Prop)
    (h : P ρ.m) : P ρ.M.mat := by
  rw [MState.mat_M]
  exact h

/-! ### R26. `ite_mul`, then `one_mul`, `zero_mul` · goal: `(if p then 1 else 0) * z` → `if p then z else 0` -/
example (p : Prop) [Decidable p] (z : ℂ) (P : ℂ → Prop) (h : P (if p then z else 0)) :
    P ((if p then 1 else 0) * z) := by
  rw [ite_mul]
  rw [one_mul, zero_mul]
  exact h

/-! ### R27. `Finset.sum_ite_eq'` · `(∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0`
The mirror image of R16: the variable is on the left of `=`. -/
example {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) (u : κ → ℂ) (P : ℂ → Prop)
    (h : P (if a ∈ Finset.univ then u a else 0)) : P (∑ x, if x = a then u x else 0) := by
  rw [Finset.sum_ite_eq']
  exact h

/-! ### R28. `RCLike.re_to_complex` · goal: `RCLike.re z` → `z.re` (for `z : ℂ`) -/
example (z : ℂ) (P : ℝ → Prop) (h : P z.re) : P (RCLike.re z) := by
  rw [RCLike.re_to_complex]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A constant diagonal `c · 1` with `c ≥ 0` is positive semidefinite: R1 → R2 → R3 → R4 → R5 → R7 -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℝ) (hc : 0 ≤ c) : 0 ≤ Dg (ι := ι) c := by
  rw [HermitianMat.zero_le_iff, Dg, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
  intro j
  rw [RCLike.ofReal_nonneg]
  exact hc

/-! ### W2. Summing one-entry diagonals entry by entry: R10, then `simp` with R11, R12, R15, R16, R17 -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) :
    (∑ k, Matrix.diagonal (fun j => if j = k then f k else 0)) = Matrix.diagonal f := by
  ext a b
  simp [Matrix.sum_apply, Matrix.diagonal_apply]

/-! ### W3. Trace of a diagonal times a matrix: R23 and R24 inside `simp` -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (M : Matrix ι ι ℂ) :
    (Matrix.diagonal v * M).trace = ∑ i, v i * M i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

/-! ### W4. Born rule for an arbitrary POVM `Λ`: R19 → R20 → R21 → R22 → R25 -/
example {X ι : Type} [Fintype X] [Fintype ι] [DecidableEq ι] (Λ : POVM X ι) (ρ : MState ι) (x : X) :
    (Λ.measure ρ x : ℝ) = RCLike.re ((Λ.mats x).mat * ρ.m).trace := by
  simp only [POVM.measure]
  simp only [ProbDistribution.mk']
  simp only [ProbDistribution.funlike_apply]
  rw [HermitianMat.inner_eq_re_trace]
  rw [MState.mat_M]

end M135Guide
