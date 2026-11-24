/- Guide for H082 (Trace distance contracts under partial trace).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`tr (MN) = tr (NM)`, the bound
`re (tr A) ≤ ‖A‖₁`, the unitary `1 ⊗ V`).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Mixed.TraceDistance

open scoped Kronecker

namespace H082Guide

/-! # Part R · Reference entries -/

/-! ## Traces and partial traces as sums (MILESTONE `trace_mul_traceRight`) -/

/-! ### R1. `simp only [Matrix.trace, Matrix.diag]` · goal: `M.trace` → `∑ i, M i i` -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (P : ℂ → Prop) (h : P (∑ i, M i i)) :
    P M.trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact h

/-! ### R2. `Matrix.mul_apply` · goal: an entry of a product → a sum over the middle index -/
example {l m n : Type} [Fintype m] (M : Matrix l m ℂ) (N : Matrix m n ℂ) (i : l) (k : n)
    (P : ℂ → Prop) (h : P (∑ j, M i j * N j k)) : P ((M * N) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R3. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β : Type} [Fintype α] [Fintype β] (g : α × β → ℂ) (P : ℂ → Prop)
    (h : P (∑ a, ∑ b, g (a, b))) : P (∑ x, g x) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R4. `Matrix.kroneckerMap_apply` · goal: an entry of `A ⊗ₖ B` → a product of entries
The infoview prints `A ⊗ₖ B` as `Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B`. -/
example {a b c e : Type} (A : Matrix a c ℂ) (B : Matrix b e ℂ) (i : a) (j : b) (k : c) (l : e)
    (P : ℂ → Prop) (h : P (A i k * B j l)) : P ((A ⊗ₖ B) (i, j) (k, l)) := by
  simp only [Matrix.kroneckerMap_apply]
  exact h

/-! ### R5. `Matrix.one_apply` · goal: an entry of the identity → `if i = j then 1 else 0` -/
example {n : Type} [DecidableEq n] (i j : n) (P : ℂ → Prop) (h : P (if i = j then 1 else 0)) :
    P ((1 : Matrix n n ℂ) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R6. `mul_ite`, `mul_one`, `mul_zero` · goal: a factor moves into both branches of an `if`
`ite_mul`, `one_mul`, `zero_mul` do the same when the `if` is the left factor. -/
example {n : Type} [DecidableEq n] (i j : n) (z : ℂ) (P : ℂ → Prop) (h : P (if i = j then z else 0)) :
    P (z * if i = j then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  exact h

/-! ### R7. `Finset.sum_ite_eq`, `Finset.mem_univ`, `if_true` · goal: a sum with one surviving term
→ that term: `∑ j, (if i = j then f j else 0)` → `f i` -/
example {n : Type} [Fintype n] [DecidableEq n] (i : n) (f : n → ℂ) (P : ℂ → Prop) (h : P (f i)) :
    P (∑ j, if i = j then f j else 0) := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact h

/-! ### R8. `Matrix.traceRight`, `Matrix.of_apply` · goal: an entry of `Tr_B A` → a sum over `d₂` -/
example {d₁ d₂ : Type} [Fintype d₂] (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i j : d₁) (P : ℂ → Prop)
    (h : P (∑ k, A (i, k) (j, k))) : P (A.traceRight i j) := by
  simp only [Matrix.traceRight, Matrix.of_apply]
  exact h

/-! ### R9. `Finset.mul_sum` · goal: a factor in front of a sum → inside every summand -/
example {α : Type} [Fintype α] (z : ℂ) (f : α → ℂ) (P : ℂ → Prop) (h : P (∑ i, z * f i)) :
    P (z * ∑ i, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ### R10. `Finset.sum_comm` · goal: swap the order of two sums (the first double sum `rw` finds) -/
example {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℂ) (P : ℂ → Prop)
    (h : P (∑ y, ∑ x, f x y)) : P (∑ x, ∑ y, f x y) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R11. `refine Finset.sum_congr rfl fun x _ => ?_` · goal: equal sums → equal summands
Context gains `x` and an unnamed `x ∈ Finset.univ`. -/
example {α : Type} [Fintype α] (f g : α → ℂ) (h : ∀ x, f x = g x) : ∑ x, f x = ∑ x, g x := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact h x

/-! ## The reduced difference (MILESTONE `traceRight_m_sub`) -/

/-! ### R12. `Matrix.traceRight_sub` · goal: `(A - B).traceRight` → `A.traceRight - B.traceRight` -/
example {d₁ d₂ : Type} [Fintype d₂] (A B : Matrix (d₁ × d₂) (d₁ × d₂) ℂ)
    (P : Matrix d₁ d₁ ℂ → Prop) (h : P (A.traceRight - B.traceRight)) :
    P (A - B).traceRight := by
  rw [Matrix.traceRight_sub]
  exact h

/-! ### R13. `rfl` · closes `ρ.traceRight.m = ρ.m.traceRight`: true by definition
(`MState.traceRight_M` states it one level down, for `ρ.M`). -/
example {dA dB : Type} [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (ρ : MState (dA × dB)) : ρ.traceRight.m = ρ.m.traceRight := by
  rfl

/-! ## Two `DecidableEq` instances (MILESTONE `unitaryGroup_congr`) -/

/-! ### R14. `obtain rfl : i1 = i2 := Subsingleton.elim _ _` · context: `i2` is replaced by `i1`
`DecidableEq α` has at most one element (a *subsingleton*), so any two instances are equal. -/
example {α : Type} (i1 i2 : DecidableEq α) (P : DecidableEq α → Prop) (h : P i1) : P i2 := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

/-! ## The main theorem -/

/-! ### R15. `unfold TrDistance` · goal: `TrDistance ρ σ` → `1 / 2 * (ρ.m - σ.m).traceNorm` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (P : ℝ → Prop)
    (h : P (1 / 2 * (ρ.m - σ.m).traceNorm)) : P (TrDistance ρ σ) := by
  unfold TrDistance
  exact h

/-! ### R16. `obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1` · context gains a
unitary `U` that attains the trace norm: `hUeq : re (tr (U * A)) = ‖A‖₁` -/
example {n : Type} [Fintype n] (A : Matrix n n ℂ) (G : Prop)
    (h : ∀ U : Matrix n n ℂ, (U * A).trace.re = A.traceNorm → G) : G := by
  obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1
  exact h U hUeq

/-! ### R17. `have hle := hS.2 ⟨b, rfl⟩` · context gains `hle : f b ≤ a`
`hS : IsGreatest S a` is `a ∈ S ∧ ∀ x ∈ S, x ≤ a`; `⟨b, rfl⟩` proves `f b ∈ {x | ∃ U, f U = x}`. -/
example {β : Type} (f : β → ℝ) (a : ℝ) (b : β) (hS : IsGreatest {x | ∃ U, f U = x} a) (G : Prop)
    (h : f b ≤ a → G) : G := by
  have hle := hS.2 ⟨b, rfl⟩
  exact h hle

/-! ### R18. `Matrix.kronecker_mem_unitary hU (one_mem _)` · context gains `U ⊗ₖ 1` unitary -/
example {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (G : Prop)
    (h : U ⊗ₖ (1 : Matrix m m ℂ) ∈ Matrix.unitaryGroup (n × m) ℂ → G) : G := by
  have hU' : U ⊗ₖ (1 : Matrix m m ℂ) ∈ Matrix.unitaryGroup (n × m) ℂ :=
    Matrix.kronecker_mem_unitary hU (one_mem _)
  exact h hU'

/-! ### R19. `dsimp only` · goal: `↑⟨U, hU⟩` (a unitary packed and unpacked) → `U`
`dsimp only at h₁ h₂` does the same in the hypotheses `h₁`, `h₂` (context). -/
example {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (P : Matrix n n ℂ → Prop) (h : P U) : P (↑(⟨U, hU⟩ : Matrix.unitaryGroup n ℂ)) := by
  dsimp only
  exact h

/-! ### R20. `rw [e] at h` · context: rewrite inside the hypothesis `h`, not the goal -/
example {α : Type} (a b : α) (e : a = b) (P : α → Prop) (h : P a) : P b := by
  rw [e] at h
  exact h

/-! ### R21. `gcongr` · goal: `c * x ≤ c * y` → `x ≤ y` (`0 ≤ c` is checked by itself)
With `hle : x ≤ y` already in the context, `gcongr` closes the goal outright. -/
example (x y : ℝ) (hxy : ∀ t : ℝ, t = y → x ≤ t) : 1 / 2 * x ≤ 1 / 2 * y := by
  gcongr
  exact hxy y rfl

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `tr (M N) = tr (N M)`: R1, R2, then R10 on the outside and R11 to reach the summand -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) : (M * N).trace = (N * M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  exact mul_comm _ _

/-! ### W2. The variational formula as a lower bound, with the candidate `U = 1`: R17 -/
example {n : Type} [Fintype n] (A : Matrix n n ℂ) : A.trace.re ≤ A.traceNorm := by
  have hle := (Matrix.traceNorm_eq_max_re_tr_U A).2 ⟨1, rfl⟩
  simpa using hle

/-! ### W3. `1 ⊗ₖ V` is unitary when `V` is: R18 with the factors swapped -/
example {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (V : Matrix m m ℂ)
    (hV : V ∈ Matrix.unitaryGroup m ℂ) :
    (1 : Matrix n n ℂ) ⊗ₖ V ∈ Matrix.unitaryGroup (n × m) ℂ :=
  Matrix.kronecker_mem_unitary (one_mem _) hV

end H082Guide
