/- Guide for H095 (Open Ising chain partition function).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (another `if`-valued function,
another nearest-neighbour sum, another weight summed over its first variable).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H095Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · A function defined by `if` on `Bool` -/

/-! ### R1. `cases b` (for `b : Bool`) · goal list: `P b` → `P false`, `P true` -/
example (P : Bool → Prop) (hf : P false) (ht : P true) (b : Bool) : P b := by
  cases b
  exacts [hf, ht]

/-- A two-valued function by `if`, like the exercise's `spin`, with other values. -/
def D (b : Bool) : ℝ := if b then 2 else 0

/-! ### R2. `simp only [D, Bool.false_eq_true, ↓reduceIte]` · goal: `D false` → the `else` branch
`simp [D]` does this by itself; `Bool.false_eq_true : (false = true) = False` decides the condition
and `↓reduceIte` drops the `if` whose condition is `True` or `False`. -/
example (P : ℝ → Prop) (h : P 0) : P (D false) := by
  simp only [D, Bool.false_eq_true, ↓reduceIte]
  exact h

/-! ## Part 2 · Splitting off the first site: `Fin.succ`, `Fin.castSucc`, `Fin.cons` -/

/-! ### R3. `Fin.sum_univ_succ` · goal: a sum over `Fin (n + 1)` → the term at `0` + the rest,
re-indexed by `i.succ` -/
example {M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M) (P : M → Prop)
    (h : P (f 0 + ∑ i : Fin n, f i.succ)) : P (∑ i, f i) := by
  rw [Fin.sum_univ_succ]
  exact h

/-! ### R4. `Fin.castSucc_zero` · goal: `Fin.castSucc 0` → `0` -/
example (n : ℕ) (P : Fin (n + 2) → Prop) (h : P 0) : P (Fin.castSucc (0 : Fin (n + 1))) := by
  rw [Fin.castSucc_zero]
  exact h

/-! ### R5. `Fin.cons_zero` · goal: `Fin.cons x p` at site `0` → `x` -/
example {α : Type} (n : ℕ) (x : α) (p : Fin n → α) (P : α → Prop) (h : P x) :
    P ((Fin.cons x p : Fin (n + 1) → α) 0) := by
  simp only [Fin.cons_zero]
  exact h

/-! ### R6. `Fin.succ_castSucc`, right to left · goal: `i.succ.castSucc` → `i.castSucc.succ`
(the same site of `Fin (n + 2)`, now written as a `succ`, so R7 applies) -/
example (n : ℕ) (i : Fin n) (P : Fin (n + 2) → Prop) (h : P i.castSucc.succ) :
    P i.succ.castSucc := by
  rw [← Fin.succ_castSucc]
  exact h

/-! ### R7. `Fin.cons_succ` · goal: `Fin.cons x p` at a site `i.succ` → `p i` -/
example {α : Type} (n : ℕ) (x : α) (p : Fin n → α) (i : Fin n) (P : α → Prop) (h : P (p i)) :
    P ((Fin.cons x p : Fin (n + 1) → α) i.succ) := by
  simp only [Fin.cons_succ]
  exact h

/-! ## Part 3 · Summing one spin out: sums over `Bool`, `cosh` -/

/-! ### R8. `rcases hs with rfl | rfl` · context loses `hs : s = 1 ∨ s = -1` and `s`;
goal list: `P s` → `P 1`, `P (-1)` -/
example (s : ℝ) (P : ℝ → Prop) (h1 : P 1) (h2 : P (-1)) (hs : s = 1 ∨ s = -1) : P s := by
  rcases hs with rfl | rfl
  exacts [h1, h2]

/-! ### R9. `Fintype.sum_bool` · goal: `∑ b : Bool, f b` → `f true + f false` -/
example {M : Type} [AddCommMonoid M] (f : Bool → M) (P : M → Prop) (h : P (f true + f false)) :
    P (∑ b, f b) := by
  rw [Fintype.sum_bool]
  exact h

/-! ### R10. `Real.cosh_eq` · goal: `cosh x` → `(exp x + exp (-x)) / 2` -/
example (x : ℝ) (P : ℝ → Prop) (h : P ((Real.exp x + Real.exp (-x)) / 2)) : P (Real.cosh x) := by
  rw [Real.cosh_eq]
  exact h

/-! ## Part 4 · Induction on the chain length: the base case -/

/-! ### R11. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: `P n` → `P 0`, `P (n + 1)`;
the second goal's context gains `ih : P n` -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  exacts [h0, hs n ih]

/-! ### R12. `Fin.sum_univ_zero` · goal: a sum over `Fin 0` (an empty chain of bonds) → `0` -/
example {M : Type} [AddCommMonoid M] (f : Fin 0 → M) (P : M → Prop) (h : P 0) : P (∑ i, f i) := by
  rw [Fin.sum_univ_zero]
  exact h

/-! ### R13. `Real.exp_zero` · goal: `exp 0` → `1` -/
example (P : ℝ → Prop) (h : P 1) : P (Real.exp 0) := by
  rw [Real.exp_zero]
  exact h

/-! ### R14. `Finset.sum_const`, then `Finset.card_univ` · goal: a sum of a constant →
(number of terms) `•` constant -/
example {α : Type} [Fintype α] (c : ℝ) (P : ℝ → Prop) (h : P (Fintype.card α • c)) :
    P (∑ _x : α, c) := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  exact h

/-! ### R15. `simp` counts configurations: `Fintype.card (Fin m → Bool)` → `2 ^ m`
(it uses `Fintype.card_pi`, `Fintype.card_bool`, `Finset.prod_const`, `nsmul_eq_mul`) -/
example (m : ℕ) (P : ℕ → Prop) (h : P (2 ^ m)) : P (Fintype.card (Fin m → Bool)) := by
  simp
  exact h

/-! ## Part 4 · The step: re-indexing the sum over configurations -/

/-- A sum over configurations, given a name by `def`, like the exercise's `Z`. -/
noncomputable def S (n : ℕ) (w : (Fin n → Bool) → ℝ) : ℝ := ∑ σ, w σ

/-! ### R16. `rw [S]` · goal: the name `S …` → its body (unfold a definition) -/
example (n : ℕ) (w : (Fin n → Bool) → ℝ) (P : ℝ → Prop) (h : P (∑ σ, w σ)) : P (S n w) := by
  rw [S]
  exact h

/-! ### R17. `Fin.consEquiv` with `Equiv.sum_comp`, right to left · goal: sum over `Fin (n + 1) → α`
→ sum over pairs `(value at site 0, values at the other n sites)` -/
example {α M : Type} [Fintype α] [AddCommMonoid M] (n : ℕ)
    (F : (Fin (n + 1) → α) → M) (P : M → Prop)
    (h : P (∑ p : α × (Fin n → α), F ((Fin.consEquiv fun _ => α) p))) : P (∑ σ, F σ) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp]
  exact h

/-! ### R18. `Fintype.sum_prod_type` · goal: a sum over pairs → a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α × β → M) (P : M → Prop)
    (h : P (∑ a, ∑ b, F (a, b))) : P (∑ p, F p) := by
  rw [Fintype.sum_prod_type]
  exact h

/-! ### R19. `Finset.sum_comm` · goal: swap the order of a double sum -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → β → M) (P : M → Prop)
    (h : P (∑ b, ∑ a, F a b)) : P (∑ a, ∑ b, F a b) := by
  rw [Finset.sum_comm]
  exact h

/-! ### R20. `refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` · goal:
`∑ x, ∑ y, f x y = ∑ x, ∑ y, g x y` → `f x y = g x y`; context gains `x`, `y` and two membership
facts `x✝ : … ∈ Finset.univ` -/
example {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f g : α → β → M)
    (h : ∀ a b, f a b = g a b) : ∑ a, ∑ b, f a b = ∑ a, ∑ b, g a b := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact h x y

/-! ### R21. `show` · goal: `(Fin.consEquiv _) (x, p)` → the same value written `Fin.cons x p`
(true by definition, so `show` accepts it; afterwards R5 and R7 can fire) -/
example {α : Type} (n : ℕ) (x : α) (p : Fin n → α) (Q : (Fin (n + 1) → α) → Prop)
    (h : Q (Fin.cons x p)) : Q ((Fin.consEquiv fun _ => α) (x, p)) := by
  show Q (Fin.cons x p : Fin (n + 1) → α)
  exact h

/-! ### R22. `Real.exp_add`, right to left · goal: `exp x * exp y` → `exp (x + y)` -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (Real.exp (x + y))) : P (Real.exp x * Real.exp y) := by
  rw [← Real.exp_add]
  exact h

/-! ### R23. `ring_nf` · closes `exp A = exp B` when `A` and `B` are equal ring expressions;
plain `ring` treats `exp A` and `exp B` as different unknowns and fails -/
example (a b c d : ℝ) : Real.exp (-a * (-b * c + d)) = Real.exp (a * b * c + -a * d) := by ring_nf

/-! ## Part 4 · The step: factoring the inner sum -/

/-! ### R24. `simp_rw [← Finset.sum_mul]` · goal: under `∑ a`, `∑ b, f a b * g a` → `(∑ b, f a b) * g a`
`rw` cannot do this: the pattern mentions the bound variable `a`, so `rw` reports
"Did not find an occurrence of the pattern". `simp_rw` rewrites under binders. -/
example {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) (g : α → ℝ) (P : ℝ → Prop)
    (h : P (∑ a, (∑ b, f a b) * g a)) : P (∑ a, ∑ b, f a b * g a) := by
  simp_rw [← Finset.sum_mul]
  exact h

/-! ### R25. `simp_rw [L _ _ (hq _)]` · goal: under a binder, rewrite with a lemma `L` that has a
hypothesis, supplied by another lemma `hq` applied to `_` (Lean fills each `_` per occurrence) -/
example {α : Type} [Fintype α] (Q : α → Prop) (f : ℝ → α → ℝ) (c : ℝ → ℝ)
    (L : ∀ (k : ℝ) (x : α), Q x → f k x = c k) (hq : ∀ x, Q x) (P : ℝ → Prop)
    (h : P (∑ _x : α, c 2)) : P (∑ x : α, f 2 x) := by
  simp_rw [L _ _ (hq _)]
  exact h

/-! ### R26. `simp_rw [← Finset.mul_sum]` · goal: `∑ i, a * f i` → `a * ∑ i, f i` (constant out) -/
example {α : Type} [Fintype α] (f : α → ℝ) (a : ℝ) (P : ℝ → Prop) (h : P (a * ∑ i, f i)) :
    P (∑ i, a * f i) := by
  simp_rw [← Finset.mul_sum]
  exact h

/-! ### R27. `rw [← S]` · goal: the body of `S` → the name `S …` (fold a definition, so that an
induction hypothesis about `S` can be used) -/
example (n : ℕ) (w : (Fin n → Bool) → ℝ) (P : ℝ → Prop) (h : P (S n w)) : P (∑ σ, w σ) := by
  rw [← S]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. An `if`-valued function takes one of its two values: R1, then R2 in each case -/
example (b : Bool) : D b = 2 ∨ D b = 0 := by
  cases b <;> simp [D]

/-! ### W2. Splitting the first term off a nearest-neighbour sum: R3, R4, R5, R6, R7
Here the "bond" between sites `i` and `i + 1` is `x_i + x_{i+1}` instead of a product of spins. -/
example (n : ℕ) (x : ℝ) (p : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), ((Fin.cons x p : Fin (n + 2) → ℝ) i.castSucc
        + (Fin.cons x p : Fin (n + 2) → ℝ) i.succ) =
      (x + p 0) + ∑ i : Fin n, (p i.castSucc + p i.succ) := by
  simp only [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]

/-! ### W3. Summing out the first variable of a sum over `Fin (n + 1) → Bool`: R17, R18 -/
example (n : ℕ) (w : Bool → ℝ) (v : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin (n + 1) → Bool, w (σ 0) * v (Fin.tail σ) =
      ∑ a : Bool, ∑ τ : Fin n → Bool, w a * v τ := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ### W4. Factoring a product weight: R19, R24, R26 -/
example (w : Bool → ℝ) (v : (Fin 3 → Bool) → ℝ) :
    ∑ a : Bool, ∑ τ : Fin 3 → Bool, w a * v τ = (∑ a, w a) * ∑ τ, v τ := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]

end H095Guide
