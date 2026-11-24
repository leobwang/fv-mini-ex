/- Guide for M062 (Irreducible quadratics).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on polynomials that are NOT the exercise's (`X ^ 3 + X`, `X ^ 4 + 1`,
`X ^ 4 - 1`).
Assumed: Lean basics.
-/
import Mathlib

open Polynomial

namespace M062Guide

/-! # Part R · Reference entries -/

/-! ## Irreducible over a field: degree goal + no-root goal -/

/-! ### R1. `compute_degree!` · closes a goal `p.natDegree = n` or `p.degree = n` for an explicit `p`
Use it inside `have hdeg : p.natDegree = n := by compute_degree!`. -/
example : (X ^ 3 + X : ℚ[X]).natDegree = 3 := by
  compute_degree!

example : (X ^ 3 + X : ℚ[X]).degree = 3 := by
  compute_degree!

/-! ### R2. `apply irreducible_of_degree_le_three_of_not_isRoot` · goal list: `Irreducible p` → two goals
`p.natDegree ∈ Finset.Icc 1 3 → (∀ x, ¬ p.IsRoot x) → Irreducible p`, over a field `K`. -/
example {K : Type} [Field K] (p : K[X]) (h1 : p.natDegree ∈ Finset.Icc 1 3)
    (h2 : ∀ x, ¬ p.IsRoot x) : Irreducible p := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  exact h1
  exact h2

/-! ### R3. `decide` · closes `n ∈ Finset.Icc a b` for numerals `n a b : ℕ` -/
example : 3 ∈ Finset.Icc 1 5 := by
  decide

/-! ### R4. `simp only [IsRoot]` · goal: `p.IsRoot x` → `eval x p = 0` (unfolds the definition) -/
example {R : Type} [Semiring R] (p : R[X]) (x : R) (h : ¬ eval x p = 0) : ¬ p.IsRoot x := by
  simp only [IsRoot]
  exact h

/-! ### R5. `eval_add` · `eval x (p + q) = eval x p + eval x q` · goal -/
example {R : Type} [Semiring R] (p q : R[X]) (x : R) (P : R → Prop) (h : P (eval x p + eval x q)) :
    P (eval x (p + q)) := by
  rw [eval_add]
  exact h

/-! ### R6. `eval_pow` · `eval x (p ^ n) = eval x p ^ n` · goal -/
example {R : Type} [CommSemiring R] (p : R[X]) (x : R) (n : ℕ) (P : R → Prop)
    (h : P (eval x p ^ n)) : P (eval x (p ^ n)) := by
  rw [eval_pow]
  exact h

/-! ### R7. `eval_X` · `eval x X = x` · goal -/
example {R : Type} [Semiring R] (x : R) (P : R → Prop) (h : P x) : P (eval x X) := by
  rw [eval_X]
  exact h

/-! ### R8. `eval_one` · `eval x 1 = 1` · goal -/
example {R : Type} [Semiring R] (x : R) (P : R → Prop) (h : P 1) : P (eval x 1) := by
  rw [eval_one]
  exact h

/-! ### R9. `positivity` · closes `0 < e`, `0 ≤ e` or `¬ e = 0` when `e` is visibly positive
(squares, sums of them, positive numerals). It does not look at the signs of variables. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) :
    ¬ a ^ 2 + b ^ 2 + 2 = 0 := by
  positivity

/-! ## Completing the square -/

/-! ### R10. `sq_nonneg` · `sq_nonneg a : 0 ≤ a ^ 2` · context gains the fact -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) (G : Prop)
    (g : 0 ≤ (a + b) ^ 2 → G) : G := by
  have h := sq_nonneg (a + b)
  exact g h

/-! ### R11. `nlinarith [t₁, …]` · closes a polynomial (in)equality, or `¬ e = 0`, from the facts `tᵢ`
It multiplies hypotheses pairwise and then does linear arithmetic over an ordered field. -/
example {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a : α) :
    ¬ a ^ 2 - 2 * a + 2 = 0 := by
  nlinarith [sq_nonneg (a - 1)]

/-! ## Not irreducible: a root forces degree 1 -/

/-! ### R12. `intro h` on `¬ A` · `¬ A` is `A → False`: context gains `h : A`, goal becomes `False` -/
example (A : Prop) (f : A → False) : ¬ A := by
  intro h
  exact f h

/-! ### R13. `Complex.I_sq` · `Complex.I ^ 2 = -1` · goal (`simp` uses it by itself) -/
example (P : ℂ → Prop) (h : P (-1)) : P (Complex.I ^ 2) := by
  rw [Complex.I_sq]
  exact h

/-! ### R14. `degree_eq_one_of_irreducible_of_root` · `Irreducible p → p.IsRoot x → p.degree = 1`
· context gains `h1 : p.degree = 1` (with `have h1 := …`). -/
example {R : Type} [CommRing R] [IsDomain R] (p : R[X]) (a : R) (hp : Irreducible p)
    (hr : p.IsRoot a) (G : Prop) (g : p.degree = 1 → G) : G := by
  have h1 := degree_eq_one_of_irreducible_of_root hp hr
  exact g h1

/-! ### R15. `rw [h] at h1` · context: rewrites the hypothesis `h1` instead of the goal -/
example {α : Type} (a b c : α) (h : a = b) (h1 : a = c) : b = c := by
  rw [h] at h1
  exact h1

/-! ### R16. `absurd` · `absurd : a → ¬ a → b` · closes any goal from a fact and its negation -/
example (A B : Prop) (ha : A) (hn : ¬ A) : B := by
  exact absurd ha hn

/-! ### R17. `decide` · closes `¬ m = n` for numerals in `WithBot ℕ` (the type of `p.degree`) -/
example : ¬ (3 : WithBot ℕ) = 1 := by
  decide

/-! # Part W · Worked combinations (not the exercise's polynomials) -/

/-! ### W1. The degree goal of R2: R1 in a `have`, `rw [hdeg]`, then R3 -/
example : (X ^ 3 + X : ℚ[X]).natDegree ∈ Finset.Icc 1 3 := by
  have hdeg : (X ^ 3 + X : ℚ[X]).natDegree = 3 := by compute_degree!
  rw [hdeg]
  decide

/-! ### W2. The no-root goal of R2: `intro x`, R4–R8 in one `simp only`, then R9 -/
example : ∀ x : ℚ, ¬ (X ^ 4 + 1 : ℚ[X]).IsRoot x := by
  intro x
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
  positivity

/-! ### W3. When `positivity` cannot see the sign (a lone `-a`), complete the square: R10 + R11 -/
example (a : ℚ) : ¬ a ^ 2 - a + 1 = 0 := by
  nlinarith [sq_nonneg (a - 1 / 2)]

/-! ### W4. Not irreducible over ℂ: a root (R13 via `simp`), R14, R1 for `degree`, R15, R16 + R17 -/
example : ¬ Irreducible (X ^ 4 - 1 : ℂ[X]) := by
  intro h
  have hroot : (X ^ 4 - 1 : ℂ[X]).IsRoot Complex.I := by simp
  have h1 := degree_eq_one_of_irreducible_of_root h hroot
  have hdeg : (X ^ 4 - 1 : ℂ[X]).degree = 4 := by compute_degree!
  rw [hdeg] at h1
  exact absurd h1 (by decide)

end M062Guide
