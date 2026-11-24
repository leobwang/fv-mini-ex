/- Guide for M094 (Mean of the binomial distribution).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's (total mass, Pascal's rule).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M094Guide

/-! # Part R · Reference entries -/

/-! ## From the integral to a finite sum -/

/-! ### R1. `integral_binomial` · goal: `∫ k, f k ∂Bin(n, q)` → a finite weighted sum over `k ≤ n`
`Bin(n, q)` is `binomial n q : Measure ℕ`; `↑q : ℝ` is the real number inside `q : unitInterval`. -/
example (n : ℕ) (q : unitInterval) (f : ℕ → ℝ) (P : ℝ → Prop)
    (h : P (∑ k ∈ Finset.Iic n, (n.choose k * (q : ℝ) ^ k * (1 - q) ^ (n - k)) • f k)) :
    P (∫ k, f k ∂(binomial n q)) := by
  rw [integral_binomial]
  exact h

/-! ### R2. `Nat.range_succ_eq_Iic` · `range (n + 1) = Iic n`; right to left: `Iic n` → `range (n + 1)`
`Finset.Iic n = {0, …, n}` and `Finset.range (n + 1) = {0, …, n}`: same set, but the sum lemmas
(R4, R14) are stated with `range`. -/
example (n : ℕ) (P : Finset ℕ → Prop) (h : P (Finset.range (n + 1))) : P (Finset.Iic n) := by
  rw [← Nat.range_succ_eq_Iic]
  exact h

/-! ## Case split on `n` -/

/-! ### R3. `rcases n with _ | m` (or `cases n with | zero => … | succ m => …`) · goal list: `n` → `0` and `m + 1` -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ m, P (m + 1)) (n : ℕ) : P n := by
  rcases n with _ | m
  exact h0
  exact hs m

/-! ## Splitting off the `k = 0` term and cleaning it -/

/-! ### R4. `Finset.sum_range_succ'` · goal: `∑ k ∈ range (n + 1), f k` → `∑ k ∈ range n, f (k + 1) + f 0` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ k ∈ Finset.range n, f (k + 1) + f 0)) : P (∑ k ∈ Finset.range (n + 1), f k) := by
  rw [Finset.sum_range_succ']
  exact h

/-! ### R5. `smul_eq_mul` · goal: `a • b` → `a * b` (scalar action of a type on itself is `*`) -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R6. `simp only [Nat.cast_zero, mul_zero, add_zero]` · goal: `s + c * ↑0` → `s` -/
example (s c : ℝ) (P : ℝ → Prop) (h : P s) : P (s + c * ((0 : ℕ) : ℝ)) := by
  simp only [Nat.cast_zero, mul_zero, add_zero]
  exact h

/-! ## The termwise identity -/

/-! ### R7. `intro k hk` on `∀ k ∈ s, Q k` · context gains `k` and `hk : k ∈ s`; goal `Q k` -/
example {ι : Type} (s : Finset ι) (Q : ι → Prop) (h : ∀ k, k ∈ s → Q k) : ∀ k ∈ s, Q k := by
  intro k hk
  exact h k hk

/-! ### R8. `Nat.add_one_mul_choose_eq` · `(n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)` in ℕ
Absorption identity: `k · C(n, k) = n · C(n - 1, k - 1)`, shifted so that no ℕ subtraction appears. -/
example (n k : ℕ) (G : Prop)
    (g : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) → G) : G := by
  have e := Nat.add_one_mul_choose_eq n k
  exact g e

/-! ### R9. `exact_mod_cast e` · closes a goal in ℝ that is the ℕ fact `e` with `↑` on every atom -/
example (a b c d : ℕ) (e : (a + 1) * b = c * (d + 1)) :
    ((a + 1 : ℕ) : ℝ) * (b : ℝ) = (c : ℝ) * ((d + 1 : ℕ) : ℝ) := by
  exact_mod_cast e

/-! ### R10. `rw [show a + 1 - (b + 1) = a - b by omega]` · goal: ℕ subtraction rewritten
`ring` treats `a + 1 - (b + 1)` (truncated ℕ subtraction) as an atom unrelated to `a - b`. -/
example (a b : ℕ) (P : ℕ → Prop) (h : P (a - b)) : P (a + 1 - (b + 1)) := by
  rw [show a + 1 - (b + 1) = a - b by omega]
  exact h

/-! ### R11. `linear_combination e * h` · closes `L = R` when `L - R = e * (h.lhs - h.rhs)` by `ring`
`h.symm` is `h` read right to left: it flips the sign of the combination. -/
example {R : Type} [CommRing R] (a b c d : R) (h : b = a) : c * a + d = c * b + d := by
  linear_combination c * h.symm

/-! ## Resumming -/

/-! ### R12. `rw [Finset.sum_congr rfl key]` · goal: `∑ k ∈ s, f k` → `∑ k ∈ s, g k`, using `key : ∀ k ∈ s, f k = g k` -/
example {ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M) (key : ∀ k ∈ s, f k = g k)
    (P : M → Prop) (h : P (∑ k ∈ s, g k)) : P (∑ k ∈ s, f k) := by
  rw [Finset.sum_congr rfl key]
  exact h

/-! ### R13. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left pulls `a` out -/
example {ι R : Type} [Semiring R] (s : Finset ι) (f : ι → R) (a : R) (P : R → Prop)
    (h : P (a * ∑ i ∈ s, f i)) : P (∑ i ∈ s, a * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R14. `add_pow` (binomial theorem) · `(x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m)`
Right to left collapses a sum of exactly this shape (factor order included) into a power. -/
example {R : Type} [CommSemiring R] (x y : R) (n : ℕ) (P : R → Prop) (h : P ((x + y) ^ n)) :
    P (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * (n.choose m : R)) := by
  rw [← add_pow]
  exact h

/-! ### R15. `add_sub_cancel` · `a + (b - a) = b` -/
example {G : Type} [AddCommGroup G] (a b : G) (P : G → Prop) (h : P b) : P (a + (b - a)) := by
  rw [add_sub_cancel]
  exact h

/-! ### R16. `one_pow` · `1 ^ n = 1` -/
example {M : Type} [Monoid M] (n : ℕ) (P : M → Prop) (h : P 1) : P ((1 : M) ^ n) := by
  rw [one_pow]
  exact h

/-! ### R17. `mul_one` · `a * 1 = a` -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's statement) -/

/-! ### W1. Total mass: the weights of `Bin(n, q)` sum to 1 (R1, R2, R5, R17, R12, R14, R15, R16) -/
example (n : ℕ) (q : unitInterval) : ∫ _k, (1 : ℝ) ∂(binomial n q) = 1 := by
  rw [integral_binomial]
  rw [← Nat.range_succ_eq_Iic]
  simp only [smul_eq_mul, mul_one]
  have key : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (q : ℝ) ^ k * (1 - q) ^ (n - k)
      = (q : ℝ) ^ k * (1 - q) ^ (n - k) * (n.choose k : ℝ) := fun k _ => by ring
  rw [Finset.sum_congr rfl key]
  rw [← add_pow]
  rw [add_sub_cancel]
  rw [one_pow]

/-! ### W2. A ℕ identity used in ℝ: cast it (R9), then `linear_combination` (R11) -/
example (n k : ℕ) (x : ℝ) :
    x * ((n + 1).choose (k + 1) : ℝ) = x * (n.choose k : ℝ) + x * (n.choose (k + 1) : ℝ) := by
  have e : ((n + 1).choose (k + 1) : ℝ) = (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ' n k
  linear_combination x * e

end M094Guide
