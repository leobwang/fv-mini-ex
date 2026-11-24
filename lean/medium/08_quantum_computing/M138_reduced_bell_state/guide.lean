/- Guide for M138 (Reduced Bell state is maximally mixed).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a general ket ψ, a general
distribution p, a basis-like vector, √(2n)).
Assumed: Lean basics.
-/
import QuantumInfo.States.Mixed.MState

open Matrix

namespace M138Guide

/-! # Part R · Reference entries -/

/-! ## From an equation of states to an equation of numbers -/

/-! ### R1. `apply MState.ext_m` · goal: `ρ = σ` (states) → `ρ.m = σ.m` (matrices) -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (h : ρ.m = σ.m) : ρ = σ := by
  apply MState.ext_m
  exact h

/-! ### R2. `ext i j` (lemma `Matrix.ext`) on `Matrix d d ℂ` · goal `A = B` → context gains `i j : d`
The index type is an arbitrary `d`, not `Fin n`, so there is no `fin_cases` afterwards. -/
example {d : Type} (A B : Matrix d d ℂ) (h : ∀ i j, A i j = B i j) : A = B := by
  ext i j
  exact h i j

/-! ### R3. `show` · goal restated in a definitionally equal form: `ρ.m` → `ρ.M.mat` (printed `↑↑ρ`)
`MState.m ρ` is *defined* as `ρ.M.mat`, so `show` accepts it; `rw` lemmas about `.M` now match. -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (i j : d)
    (h : ρ.M.mat i j = σ.M.mat i j) : ρ.m i j = σ.m i j := by
  show ρ.M.mat i j = σ.M.mat i j
  exact h

/-! ## Unwrapping the left side: partial trace of a state -/

/-! ### R4. `MState.traceLeft_M` · goal: `↑ρ.traceLeft` → `(↑ρ).traceLeft` (state level → HermitianMat level) -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ : MState (d₁ × d₂)) (P : HermitianMat d₂ ℂ → Prop) (h : P ρ.M.traceLeft) :
    P ρ.traceLeft.M := by
  rw [MState.traceLeft_M]
  exact h

/-! ### R5. `HermitianMat.traceLeft_mat` · goal: `↑A.traceLeft` → `(↑A).traceLeft` (HermitianMat → Matrix) -/
example {d₁ d₂ : Type} [Fintype d₁] (A : HermitianMat (d₁ × d₂) ℂ)
    (P : Matrix d₂ d₂ ℂ → Prop) (h : P A.mat.traceLeft) : P A.traceLeft.mat := by
  rw [HermitianMat.traceLeft_mat]
  exact h

/-! ### R6. `MState.mat_M` · goal: `↑↑ρ` (that is `ρ.M.mat`) → `ρ.m` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d)
    (P : Matrix d d ℂ → Prop) (h : P ρ.m) : P ρ.M.mat := by
  rw [MState.mat_M]
  exact h

/-! ## Unwrapping the right side: the maximally mixed state -/

/-! ### R7. `rw [MState.uniform]` · goal: the name `MState.uniform` → its body `ofClassical uniform` -/
example {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (P : MState d → Prop)
    (h : P (MState.ofClassical ProbDistribution.uniform)) : P MState.uniform := by
  rw [MState.uniform]
  exact h

/-! ### R8. `MState.coe_ofClassical` · goal: `↑(ofClassical p)` → `HermitianMat.diagonal ℂ (p ·)` -/
example {d : Type} [Fintype d] [DecidableEq d] (p : ProbDistribution d)
    (P : HermitianMat d ℂ → Prop) (h : P (HermitianMat.diagonal ℂ fun x => (p x : ℝ))) :
    P (MState.ofClassical p).M := by
  rw [MState.coe_ofClassical]
  exact h

/-! ### R9. `HermitianMat.diagonal_mat` · goal: `↑(HermitianMat.diagonal ℂ f)` → `Matrix.diagonal (↑f ·)` -/
example {d : Type} [DecidableEq d] (f : d → ℝ) (P : Matrix d d ℂ → Prop)
    (h : P (Matrix.diagonal fun x => (f x : ℂ))) : P (HermitianMat.diagonal ℂ f).mat := by
  rw [HermitianMat.diagonal_mat]
  exact h

/-! ### R10. `Matrix.diagonal_apply` · goal: entry `diagonal f i j` → `if i = j then f i else 0` -/
example {d : Type} [DecidableEq d] (f : d → ℂ) (i j : d) (P : ℂ → Prop)
    (h : P (if i = j then f i else 0)) : P (Matrix.diagonal f i j) := by
  rw [Matrix.diagonal_apply]
  exact h

/-! ## The partial trace as a sum -/

/-! ### R11. `simp only [Matrix.traceLeft]` · goal: `A.traceLeft i j` → `of (fun i₁ j₁ => ∑ i₂, …) i j` -/
example {d₁ d₂ : Type} [Fintype d₁] (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i j : d₂) (P : ℂ → Prop)
    (h : P (∑ k, A (k, i) (k, j))) : P (A.traceLeft i j) := by
  simp only [Matrix.traceLeft]
  exact h

/-! ### R12. `Matrix.of_apply` · goal: `of f i j` → `f i j` (then Lean β-reduces the `fun`) -/
example {d : Type} (f : d → d → ℂ) (i j : d) (P : ℂ → Prop) (h : P (f i j)) :
    P (Matrix.of f i j) := by
  rw [Matrix.of_apply]
  exact h

/-! ### R13. `simp only [MState.pure_apply]` · goal: `(pure ψ).m i j` → `ψ i * conj (ψ j)`, also under `∑`
`rw` cannot rewrite under the bound variable of `∑`; `simp only` can. -/
example {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i : d) (P : ℂ → Prop)
    (h : P (∑ k, ψ k * (starRingEnd ℂ) (ψ i))) : P (∑ k, (MState.pure ψ).m k i) := by
  simp only [MState.pure_apply]
  exact h

/-! ## Case split on the index -/

/-! ### R14. `by_cases h : i = j` · goal list: one goal → two, with `h : i = j` and `h : ¬i = j` -/
example {d : Type} (i j : d) (G : Prop) (hp : i = j → G) (hn : ¬i = j → G) : G := by
  by_cases h : i = j
  · exact hp h
  · exact hn h

/-! ### R15. `subst h` · context: `h : i = j` and `j` disappear; every `j` becomes `i` -/
example {d : Type} (i j : d) (P : d → d → Prop) (hii : ∀ x, P x x) (h : i = j) : P i j := by
  subst h
  exact hii i

/-! ## Evaluating the maximally entangled state (`simp [Ket.MES, Ket.apply]` applies R16–R23) -/

/-! ### R16. `Ket.apply` · goal: `ψ x` (a ket used as a function) → `ψ.vec x` (its stored vector) -/
example {d : Type} [Fintype d] (ψ : Ket d) (x : d) (P : ℂ → Prop) (h : P (ψ.vec x)) : P (ψ x) := by
  rw [Ket.apply]
  exact h

/-! ### R17. `simp only [Ket.MES]` · goal: `(Ket.MES d).vec (x, y)` → `if x = y then 1 / ↑√↑(Fintype.card d) else 0`
The `if` inside `Ket.MES` is decided classically, hence `open Classical in` for this example only. -/
open Classical in
example {d : Type} [Fintype d] [Nonempty d] (x y : d) (P : ℂ → Prop)
    (h : P (if x = y then 1 / (Real.sqrt (Fintype.card d) : ℂ) else 0)) :
    P ((Ket.MES d).vec (x, y)) := by
  simp only [Ket.MES]
  exact h

/-! ### R18. `one_div` · `1 / a = a⁻¹` · goal: `1 / a` → `a⁻¹` -/
example {α : Type} [DivInvMonoid α] (a : α) (P : α → Prop) (h : P a⁻¹) : P (1 / a) := by
  rw [one_div]
  exact h

/-! ### R19. `ite_mul`, then `zero_mul` · goal: `(if c then a else 0) * b` → `if c then a * b else 0` -/
example {α : Type} [MulZeroClass α] (c : Prop) [Decidable c] (a b : α) (P : α → Prop)
    (h : P (if c then a * b else 0)) : P ((if c then a else 0) * b) := by
  rw [ite_mul]
  rw [zero_mul]
  exact h

/-! ### R20. `Finset.sum_ite_eq'`, then `Finset.mem_univ` · goal: `∑ x, if x = a then b x else 0` → `b a`
Only the term `x = a` survives. `if_pos (Finset.mem_univ a)` removes the leftover `a ∈ univ` test. -/
example {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (a : ι) (b : ι → M)
    (P : M → Prop) (h : P (b a)) : P (∑ x, if x = a then b x else 0) := by
  rw [Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ a)]
  exact h

/-! ### R21. `map_inv₀`, then `Complex.conj_ofReal` · goal: `conj (↑r)⁻¹` → `(↑r)⁻¹` -/
example (r : ℝ) (P : ℂ → Prop) (h : P (r : ℂ)⁻¹) : P ((starRingEnd ℂ) (r : ℂ)⁻¹) := by
  rw [map_inv₀]
  rw [Complex.conj_ofReal]
  exact h

/-! ### R22. `ProbDistribution.uniform_def`, then `Finset.card_univ` · goal: `↑(uniform y)` → `1 / ↑(Fintype.card α)` -/
example {α : Type} [Fintype α] [Nonempty α] (y : α) (P : ℝ → Prop)
    (h : P (1 / (Fintype.card α : ℝ))) : P (ProbDistribution.uniform y : ℝ) := by
  rw [ProbDistribution.uniform_def]
  rw [Finset.card_univ]
  exact h

/-! ### R23. `if_pos`, `if_neg` · goal: an `if` whose condition is decided → one branch
`simp` decides `i = i` by itself; for `i = j` it needs `h : ¬i = j` in its list. -/
example {α : Type} {d : Type} [DecidableEq d] (i j : d) (a b : α) (P : α → Prop)
    (ha : P a) (hb : P b) (h : ¬i = j) : P (if i = i then a else b) ∧ P (if i = j then a else b) := by
  rw [if_pos rfl]
  rw [if_neg h]
  exact ⟨ha, hb⟩

/-! ## The √ fact: `(√n)⁻¹ * (√n)⁻¹ = n⁻¹` -/

/-! ### R24. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; used right to left: `rw [← mul_inv]` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (P : α → Prop) (h : P (a * b)⁻¹) :
    P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R25. `Complex.ofReal_mul` · `↑(x * y) = ↑x * ↑y`; right to left moves `*` inside the cast -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ↑(x * y)) : P (↑x * ↑y) := by
  rw [← Complex.ofReal_mul]
  exact h

/-! ### R26. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal rewritten, plus side goal `0 ≤ x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P x) (hx : 0 ≤ x) : P (√x * √x) := by
  rw [Real.mul_self_sqrt]
  exact h
  exact hx

/-! ### R27. `Nat.cast_nonneg` · closes `0 ≤ ↑n` for a natural number `n` cast into `ℝ`
Use it as the argument of R26: `rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]`. -/
example (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := by
  exact Nat.cast_nonneg n

/-! ### R28. `Complex.ofReal_natCast` · goal: `↑↑n` (ℕ → ℝ → ℂ) → `↑n` (ℕ → ℂ directly) -/
example (n : ℕ) (P : ℂ → Prop) (h : P (n : ℂ)) : P ((n : ℝ) : ℂ) := by
  rw [Complex.ofReal_natCast]
  exact h

/-! ## Off the diagonal -/

/-! ### R29. `map_zero`, then `mul_zero` · goal: `a * conj 0` → `0` -/
example (a : ℂ) (P : ℂ → Prop) (h : P 0) : P (a * (starRingEnd ℂ) 0) := by
  rw [map_zero]
  rw [mul_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The right-side unwrap on a general distribution `p`: R3, R8, R9, R10
The two sides then print identically, but `rw` does not close the goal on its own: on the left `↑`
is `RCLike.ofReal` (`HermitianMat.diagonal` works over any `RCLike 𝕜`), on the right it is
`Complex.ofReal`. They are equal by unfolding, which `rfl` checks. -/
example {d : Type} [Fintype d] [DecidableEq d] (p : ProbDistribution d) (i j : d) :
    (MState.ofClassical p).m i j = if i = j then ((p i : ℝ) : ℂ) else 0 := by
  show (MState.ofClassical p).M.mat i j = _
  rw [MState.coe_ofClassical]
  rw [HermitianMat.diagonal_mat]
  rw [Matrix.diagonal_apply]
  rfl

/-! ### W2. The left-side unwrap on a general ket `ψ` on `d₁ × d₂`: R3–R6, R11–R13 -/
example {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (i j : d₂) :
    (MState.pure ψ).traceLeft.m i j = ∑ k, ψ (k, i) * (starRingEnd ℂ) (ψ (k, j)) := by
  show (MState.pure ψ).traceLeft.M.mat i j = _
  rw [MState.traceLeft_M, HermitianMat.traceLeft_mat, MState.mat_M]
  simp only [Matrix.traceLeft, Matrix.of_apply]
  simp only [MState.pure_apply]

/-! ### W3. Collapsing a sum of indicator products with one `simp` (R19, R20, R21, R23) -/
example {d : Type} [Fintype d] [DecidableEq d] (a : d) (c : ℝ) :
    ∑ x, (if x = a then (c : ℂ) else 0) * (starRingEnd ℂ) (if x = a then (c : ℂ) else 0) =
      (c : ℂ) * c := by
  simp

/-! ### W4. The √ fact for `√(2n)`, step by step: R24, R25, R26 with R27, R28 -/
example (n : ℕ) :
    (Real.sqrt ((2 * n : ℕ) : ℝ) : ℂ)⁻¹ * (Real.sqrt ((2 * n : ℕ) : ℝ) : ℂ)⁻¹ =
      ((2 * n : ℕ) : ℂ)⁻¹ := by
  rw [← mul_inv]
  rw [← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [Complex.ofReal_natCast]

end M138Guide
