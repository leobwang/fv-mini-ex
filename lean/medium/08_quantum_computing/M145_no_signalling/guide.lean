/- Guide for M145 (No-signalling).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Index types are placeholders too: `k m n ι : Type`, each with the `Fintype` (finite) or `DecidableEq`
(equality is decidable, needed for the identity matrix `1`) instance the lemma asks for.
Part W: worked combinations on objects that are NOT the exercise's (`trace`, `1 ⊗ₖ B`, other sums).
Assumed: Lean basics.
-/
import QuantumInfo.ForMathlib.Matrix

open Matrix
open scoped Kronecker

namespace M145Guide

/-! # Part R · Reference entries -/

/-! ## Matrix equations and the partial trace -/

/-! ### R1. `ext x y` (lemma `Matrix.ext`) · goal `A = B` → context gains `x y`, goal is one entry
Works for any index types, not only `Fin n`. -/
example {m n : Type} (A B : Matrix m n ℂ) (h : ∀ x y, A x y = B x y) : A = B := by
  ext x y
  exact h x y

/-! ### R2. `Matrix.traceLeft`, `Matrix.of_apply` · goal: an entry of `N.traceLeft` → a sum
`traceLeft` (physlib) traces out the FIRST factor of a product index:
`N.traceLeft x y = ∑ i, N (i, x) (i, y)`. Its body is `Matrix.of fun x y ↦ …`; `of_apply` evaluates it. -/
example {k m n : Type} [Fintype k] (N : Matrix (k × m) (k × n) ℂ) (x : m) (y : n) (P : ℂ → Prop)
    (h : P (∑ i, N (i, x) (i, y))) : P (N.traceLeft x y) := by
  simp only [Matrix.traceLeft]
  simp only [Matrix.of_apply]
  exact h

/-! ### R3. `Matrix.sum_apply` · goal: entry of a sum of matrices → sum of the entries -/
example {m n ι : Type} [Fintype ι] (f : ι → Matrix m n ℂ) (x : m) (y : n) (P : ℂ → Prop)
    (h : P (∑ c, f c x y)) : P ((∑ c, f c) x y) := by
  rw [Matrix.sum_apply]
  exact h

/-! ### R4. `Finset.sum_comm` · goal: swap two nested sums -/
example {m ι : Type} [Fintype m] [Fintype ι] (g : ι → m → ℂ) (P : ℂ → Prop)
    (h : P (∑ y, ∑ x, g x y)) : P (∑ x, ∑ y, g x y) := by
  rw [Finset.sum_comm]
  exact h

/-! ## Entries of products, Kronecker products and the identity -/

/-! ### R5. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {l m n : Type} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) (i : l) (k : n)
    (P : ℂ → Prop) (h : P (∑ j, A i j * B j k)) : P ((A * B) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R6. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {m n : Type} [Fintype m] [Fintype n] (f : m × n → ℂ) (P : ℂ → Prop)
    (h : P (∑ x, ∑ y, f (x, y))) : P (∑ p, f p) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R7. `Matrix.kroneckerMap_apply` · goal: entry of `A ⊗ₖ B` → product of entries
`A ⊗ₖ B` prints as `kroneckerMap (fun x1 x2 => x1 * x2) A B`. -/
example {m n : Type} (A : Matrix m m ℂ) (B : Matrix n n ℂ) (a c : m) (b e : n) (P : ℂ → Prop)
    (h : P (A a c * B b e)) : P ((A ⊗ₖ B) (a, b) (c, e)) := by
  simp only [Matrix.kroneckerMap_apply]
  exact h

/-! ### R8. `Matrix.one_apply` · goal: entry of the identity → `if i = j then 1 else 0` -/
example {n : Type} [DecidableEq n] (i j : n) (P : ℂ → Prop) (h : P (if i = j then 1 else 0)) :
    P ((1 : Matrix n n ℂ) i j) := by
  rw [Matrix.one_apply]
  exact h

/-! ### R9. `mul_ite`, `ite_mul` · goal: pull an `if` out of a product -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop)
    (h : P (if c then a * 1 * b else a * 0 * b)) : P (a * (if c then 1 else 0) * b) := by
  rw [mul_ite]
  rw [ite_mul]
  exact h

/-! ### R10. `mul_one`, `mul_zero`, `zero_mul` · goal: clean the branches -/
example (c : Prop) [Decidable c] (a b : ℂ) (P : ℂ → Prop) (h : P (if c then a * b else 0)) :
    P (if c then a * 1 * b else a * 0 * b) := by
  simp only [mul_one, mul_zero, zero_mul]
  exact h

/-! ### R11. `Finset.sum_ite_eq`, `Finset.sum_ite_eq'` · goal: a sum of `if a = x` collapses to one term
`sum_ite_eq` is for `if a = x`, `sum_ite_eq'` for `if x = a`. -/
example {n : Type} [Fintype n] [DecidableEq n] (a : n) (f : n → ℂ) (P : ℂ → ℂ → Prop)
    (h : P (if a ∈ Finset.univ then f a else 0) (if a ∈ Finset.univ then f a else 0)) :
    P (∑ x, if a = x then f x else 0) (∑ x, if x = a then f x else 0) := by
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
  exact h

/-! ### R12. `Finset.mem_univ`, `if_true` · goal: `if a ∈ univ then t else e` → `t` -/
example {n : Type} [Fintype n] [DecidableEq n] (a : n) (t e : ℂ) (P : ℂ → Prop) (h : P t) :
    P (if a ∈ Finset.univ then t else e) := by
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ### R13. `Finset.sum_congr` · goal: two sums equal → one term equal (context gains `x`) -/
example {n : Type} [Fintype n] (f g : n → ℂ) (h : ∀ x, f x = g x) : ∑ x, f x = ∑ x, g x := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact h x

/-! ### R14. `mul_comm` · `a * b = b * a` · goal: swap two factors (or close `a * b = b * a`) -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! ## Rewriting matrix expressions -/

/-! ### R15. `Matrix.mul_assoc` · `A * B * C = A * (B * C)` · goal: regroup a product -/
example {n : Type} [Fintype n] (A B C : Matrix n n ℂ) (P : Matrix n n ℂ → Prop)
    (h : P (A * (B * C))) : P (A * B * C) := by
  rw [Matrix.mul_assoc]
  exact h

/-! ### R16. `simp_rw [l]` · goal: rewrite with `l` also under a binder such as `∑ i, …`
`rw` cannot rewrite a term that mentions the bound variable `i`; `simp_rw` can. -/
example {n ι : Type} [Fintype n] [Fintype ι] (A C : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (P : Matrix n n ℂ → Prop) (h : P (∑ i, A * (B i * C))) : P (∑ i, A * B i * C) := by
  simp_rw [Matrix.mul_assoc]
  exact h

/-! ### R17. `Matrix.conjTranspose_kronecker` · goal: `(A ⊗ₖ B)ᴴ` → `Aᴴ ⊗ₖ Bᴴ` -/
example {m n : Type} (A : Matrix m m ℂ) (B : Matrix n n ℂ) (P : Matrix (m × n) (m × n) ℂ → Prop)
    (h : P (Aᴴ ⊗ₖ Bᴴ)) : P (A ⊗ₖ B)ᴴ := by
  rw [Matrix.conjTranspose_kronecker]
  exact h

/-! ### R18. `Matrix.conjTranspose_one` · goal: `1ᴴ` → `1` -/
example {n : Type} [DecidableEq n] (P : Matrix n n ℂ → Prop) (h : P 1) : P (1 : Matrix n n ℂ)ᴴ := by
  rw [Matrix.conjTranspose_one]
  exact h

/-! ### R19. `Matrix.mul_kronecker_mul` · `(A * A') ⊗ₖ (B * B') = A ⊗ₖ B * A' ⊗ₖ B'`;
right to left (`rw [← Matrix.mul_kronecker_mul]`) merges a product of Kronecker products -/
example {m n : Type} [Fintype m] [Fintype n] (A A' : Matrix m m ℂ) (B B' : Matrix n n ℂ)
    (P : Matrix (m × n) (m × n) ℂ → Prop) (h : P ((A * A') ⊗ₖ (B * B'))) :
    P (A ⊗ₖ B * A' ⊗ₖ B') := by
  rw [← Matrix.mul_kronecker_mul]
  exact h

/-! ### R20. `Matrix.one_mul` · goal: `1 * A` → `A` -/
example {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (P : Matrix n n ℂ → Prop)
    (h : P A) : P (1 * A) := by
  rw [Matrix.one_mul]
  exact h

/-! ### R21. `Matrix.mul_sum` · `A * ∑ i, f i = ∑ i, A * f i`; right to left pulls `A *` out of a sum -/
example {n ι : Type} [Fintype n] [Fintype ι] (A : Matrix n n ℂ) (f : ι → Matrix n n ℂ)
    (P : Matrix n n ℂ → Prop) (h : P (A * ∑ i, f i)) : P (∑ i, A * f i) := by
  rw [← Matrix.mul_sum]
  exact h

/-! ### R22. `Matrix.one_kronecker_one` · `1 ⊗ₖ 1 = 1`; right to left splits the identity of a pair type -/
example {m n : Type} [DecidableEq m] [DecidableEq n] (P : Matrix (m × n) (m × n) ℂ → Prop)
    (h : P ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ))) : P (1 : Matrix (m × n) (m × n) ℂ) := by
  rw [← Matrix.one_kronecker_one]
  exact h

/-! ### R23. `ext ⟨a, b⟩ ⟨c, e⟩` · goal `A = B` on pair indices → context gains `a b c e`, one entry -/
example {m n : Type} (A B : Matrix (m × n) (m × n) ℂ)
    (h : ∀ a b c e, A (a, b) (c, e) = B (a, b) (c, e)) : A = B := by
  ext ⟨a, b⟩ ⟨c, e⟩
  exact h a b c e

/-! ### R24. `Finset.sum_mul` · `(∑ i, f i) * b = ∑ i, f i * b` · goal: distribute a factor into a sum -/
example {ι : Type} [Fintype ι] (f : ι → ℂ) (b : ℂ) (P : ℂ → Prop) (h : P (∑ i, f i * b)) :
    P ((∑ i, f i) * b) := by
  rw [Finset.sum_mul]
  exact h

/-! ### R25. `Matrix.mul_one` · goal: `A * 1` → `A` -/
example {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (P : Matrix n n ℂ → Prop)
    (h : P A) : P (A * 1) := by
  rw [Matrix.mul_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The full trace is additive: unfold, R3, then R4 closes it -/
example {n ι : Type} [Fintype n] [Fintype ι] (f : ι → Matrix n n ℂ) :
    (∑ i, f i).trace = ∑ i, (f i).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]
  exact Finset.sum_comm

/-! ### W2. The identity collapses a sum: R8, R9, R10, R11, R12 -/
example {n : Type} [Fintype n] [DecidableEq n] (v : n → ℂ) (i : n) :
    ∑ j, (1 : Matrix n n ℂ) i j * v j = v i := by
  simp only [Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ### W3. Merge Kronecker products under a sum: R16 with R17, R18, R19, R20 -/
example {m n ι : Type} [Fintype m] [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix m m ℂ) (B : Matrix m m ℂ) :
    ∑ i, (A i ⊗ₖ (1 : Matrix n n ℂ))ᴴ * (B ⊗ₖ (1 : Matrix n n ℂ))
      = ∑ i, ((A i)ᴴ * B) ⊗ₖ (1 : Matrix n n ℂ) := by
  simp_rw [Matrix.conjTranspose_kronecker]
  simp_rw [Matrix.conjTranspose_one]
  simp_rw [← Matrix.mul_kronecker_mul]
  simp_rw [Matrix.one_mul]

/-! ### W4. A sum of Kronecker products, entry by entry: R23, then `simp` with R3, R7 and
`Finset.mul_sum` (the mirror of R24: `b * ∑ i, f i = ∑ i, b * f i`) -/
example {m n ι : Type} [Fintype ι] [DecidableEq m] (f : ι → Matrix n n ℂ) :
    ∑ i, (1 : Matrix m m ℂ) ⊗ₖ f i = (1 : Matrix m m ℂ) ⊗ₖ ∑ i, f i := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

end M145Guide
