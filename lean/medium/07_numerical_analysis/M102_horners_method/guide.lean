/- Guide for M102 (Horner's method).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Induction alternatives are written `| cons c cs ih => ?_` so that each case stays open as a goal you
can inspect; in the exercise you write tactics after `=>` instead.
Part W: worked combinations on objects that are NOT the exercise's (a plain list sum, squares).
Assumed: Lean basics.
-/
import Mathlib

open Polynomial

namespace M102Guide

/-- A list function with the same shape of recursion as the exercise's, used by R2, R3 and W1. -/
def total : List ℝ → ℝ
  | [] => 0
  | c :: cs => c + total cs

/-! # Part R · Reference entries -/

/-! ## Induction on a list and unfolding a recursive definition -/

/-! ### R1. `induction xs with | nil => … | cons c cs ih => …` · goal list: one goal per constructor
The `cons` case names the head `c`, the tail `cs` and the induction hypothesis `ih : P cs`. -/
example (P : List ℝ → Prop) (h0 : P []) (hs : ∀ c cs, P cs → P (c :: cs)) (xs : List ℝ) :
    P xs := by
  induction xs with
    | nil => ?_
    | cons c cs ih => ?_
  · exact h0
  · exact hs c cs ih

/-! ### R2. `simp [D]` on the `nil` case · closes it
`simp` unfolds `D []`, rewrites `[].length` to `0` (`List.length_nil`), `Finset.range 0` to `∅`
(`Finset.range_zero`) and a sum over `∅` to `0`; then both sides are `0`. -/
example (f : ℕ → ℝ) : total [] = ∑ i ∈ Finset.range ([] : List ℝ).length, f i := by
  simp [total]

/-! ### R3. `rw [D]` on `D (c :: cs)` · goal: the call → the right-hand side of D's `cons` equation -/
example (c : ℝ) (cs : List ℝ) (P : ℝ → Prop) (h : P (c + total cs)) : P (total (c :: cs)) := by
  rw [total]
  exact h

/-! ### R4. `List.length_cons` · `(a :: as).length = as.length + 1` -/
example {α : Type} (a : α) (as : List α) (P : ℕ → Prop) (h : P (as.length + 1)) :
    P (a :: as).length := by
  rw [List.length_cons]
  exact h

/-! ## Sums over `Finset.range` -/

/-! ### R5. `Finset.sum_range_succ'` · `∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0`
Peels off the FIRST term (`k = 0`) and shifts the index of the rest. (Unprimed `Finset.sum_range_succ`
peels off the last term instead.) -/
example {β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) (P : β → Prop)
    (h : P (∑ k ∈ Finset.range n, f (k + 1) + f 0)) : P (∑ k ∈ Finset.range (n + 1), f k) := by
  rw [Finset.sum_range_succ']
  exact h

/-! ### R6. `Finset.mul_sum` · `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` · goal: factor moves into the sum -/
example {ι β : Type} [NonUnitalNonAssocSemiring β] (s : Finset ι) (f : ι → β) (a : β)
    (P : β → Prop) (h : P (∑ i ∈ s, a * f i)) : P (a * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact h

/-! ## Reading list entries with `getD` -/

/-! ### R7. `List.getD_cons_succ` · `(c :: cs).getD (n + 1) d = cs.getD n d` -/
example {α : Type} (c d : α) (cs : List α) (n : ℕ) (P : α → Prop) (h : P (cs.getD n d)) :
    P ((c :: cs).getD (n + 1) d) := by
  rw [List.getD_cons_succ]
  exact h

/-! ### R8. `List.getD_cons_zero` · `(c :: cs).getD 0 d = c` -/
example {α : Type} (c d : α) (cs : List α) (P : α → Prop) (h : P c) : P ((c :: cs).getD 0 d) := by
  rw [List.getD_cons_zero]
  exact h

/-! ## Powers and the shape of each term -/

/-! ### R9. `pow_zero`, then `mul_one` · `a ^ 0 = 1`, `b * 1 = b` -/
example {M : Type} [Monoid M] (a b : M) (P : M → Prop) (h : P b) : P (b * a ^ 0) := by
  rw [pow_zero]
  rw [mul_one]
  exact h

/-! ### R10. `pow_succ` · `a ^ (n + 1) = a ^ n * a` (the new factor goes on the RIGHT) -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R11. `rw [add_comm]` · `a + b = b + a` · goal: the FIRST sum it meets is swapped
With no arguments it matches the first `_ + _` in the goal, reading left to right (here the left
side). Pin it down with `add_comm a b` if it picks the wrong one. -/
example {β : Type} [AddCommMagma β] (a b c : β) (h : b + a = c) : a + b = c := by
  rw [add_comm]
  exact h

/-! ### R12. `congr 1` · goal `f a b = f a' b'` → goals `a = a'`, `b = b'`; equal parts close by `rfl`
It also closes a part by `assumption` when a hypothesis states it exactly. -/
example (a b c : ℝ) (h : b = a) : a + c = b + c := by
  congr 1
  exact h.symm

/-! ### R13. `refine Finset.sum_congr rfl fun i hi => ?_` · goal: two sums over `s` → one term,
context gains `i` and `hi : i ∈ s`
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`. -/
example {ι β : Type} [AddCommMonoid β] (s : Finset ι) (f g : ι → β) (h : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  exact h i hi

/-! ## Polynomials -/

/-! ### R14. `Polynomial.eval_eq_sum_range` · `eval x p = ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ i` -/
example (p : ℝ[X]) (x : ℝ) (P : ℝ → Prop)
    (h : P (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i)) : P (p.eval x) := by
  rw [Polynomial.eval_eq_sum_range]
  exact h

/-! ### R15. `List.length_map` · `(List.map f l).length = l.length` -/
example {α β : Type} (f : α → β) (l : List α) (P : ℕ → Prop) (h : P l.length) :
    P (l.map f).length := by
  rw [List.length_map]
  exact h

/-! ### R16. `List.length_range` · `(List.range n).length = n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (List.range n).length := by
  rw [List.length_range]
  exact h

/-! ### R17. `rw [Finset.mem_range] at hi` · context: `hi : i ∈ range n` → `hi : i < n` -/
example (i n : ℕ) (hi : i ∈ Finset.range n) (G : Prop) (h : i < n → G) : G := by
  rw [Finset.mem_range] at hi
  exact h hi

/-! ## One entry of a mapped list (`simp [List.getD_eq_getElem?_getD, hi]` chains R18–R22) -/

/-! ### R18. `List.getD_eq_getElem?_getD` · `l.getD i d = l[i]?.getD d` -/
example {α : Type} (l : List α) (i : ℕ) (d : α) (P : α → Prop) (h : P (l[i]?.getD d)) :
    P (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  exact h

/-! ### R19. `getElem?_pos` · `l[i]? = some l[i]`, given `hl : i < l.length` -/
example {α : Type} (l : List α) (i : ℕ) (hl : i < l.length) (P : Option α → Prop)
    (h : P (some l[i])) : P l[i]? := by
  rw [getElem?_pos l i hl]
  exact h

/-! ### R20. `Option.getD_some` · `(some a).getD d = a` -/
example {α : Type} (a d : α) (P : α → Prop) (h : P a) : P ((some a).getD d) := by
  rw [Option.getD_some]
  exact h

/-! ### R21. `List.getElem_map` · `(List.map f l)[i] = f l[i]` -/
example {α β : Type} (f : α → β) (l : List α) (i : ℕ) (hl : i < (l.map f).length)
    (P : β → Prop) (h : P (f (l[i]'(by simpa using hl)))) : P ((l.map f)[i]'hl) := by
  rw [List.getElem_map]
  exact h

/-! ### R22. `List.getElem_range` · `(List.range n)[j] = j` -/
example (n j : ℕ) (hj : j < (List.range n).length) (P : ℕ → Prop) (h : P j) :
    P ((List.range n)[j]'hj) := by
  rw [List.getElem_range]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A list sum as a `getD`-sum, by induction: R1, R2, R3, `rw [ih]`, R4, R5, R7, R8, R11 -/
example (cs : List ℝ) : total cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 := by
  induction cs with
    | nil => simp [total]
    | cons c cs ih =>
      rw [total, ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_comm]

/-! ### W2. Termwise sum equality: R12, R13, then `ring` -/
example (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 * (f i * 3) + 1 = ∑ i ∈ Finset.range n, 6 * f i + 1 := by
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  ring

/-! ### W3. Reading one entry of a mapped `List.range`: R18–R22 in one `simp` -/
example (i : ℕ) (hi : i < 5) :
    ((List.range 5).map (fun k : ℕ => (k : ℝ) ^ 2)).getD i 0 = (i : ℝ) ^ 2 := by
  simp [List.getD_eq_getElem?_getD, hi]

end M102Guide
