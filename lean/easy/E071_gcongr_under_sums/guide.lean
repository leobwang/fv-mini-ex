/- Guide for E071 (gcongr under sums).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal". A hypothesis `k` in an entry is only there to finish the
example; it shows what the context became.
Part W: worked combinations on objects that are NOT the exercise's (other terms, other index sets).
Assumed: Lean basics (E001–E033). Sums, products and `range` are explained in the entries.
-/
import Mathlib

open Finset

namespace E071Guide

/-! # Part R · Reference entries -/

/-! ## Comparing two sums term by term -/

/-! ### R1. `gcongr with i hi` on a sum · goal: `∑ ≤ ∑` → one term; context gains `i`, `hi`
`s : Finset ι` is a finite set of indices; `∑ i ∈ s, f i` adds `f i` over every `i ∈ s`.
`gcongr` sees that both sides are `∑ i ∈ s, _` and reduces the goal to the terms that differ.
`with i hi` names the new index and its membership proof `hi : i ∈ s`. -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  gcongr with i hi
  exact h i hi

/-! ## Using a `∀` hypothesis at one index -/

/-! ### R2. `h a` / `h a ha` · instantiate a `∀`: closes the goal, or the context gains the instance
`∀ i, P i` applied to `a` proves `P a`. `∀ i ∈ s, P i` means `∀ i, i ∈ s → P i`, so it takes two
arguments: the index `a` and a proof `ha : a ∈ s`. -/
example {ι : Type} (P : ι → Prop) (h : ∀ i, P i) (a : ι) : P a := by
  exact h a

example {ι : Type} (s : Finset ι) (P : ι → Prop) (Q : Prop) (h : ∀ i ∈ s, P i) (a : ι)
    (ha : a ∈ s) (k : P a → Q) : Q := by
  have hP := h a ha
  exact k hP

/-! ## Nonlinear arithmetic -/

/-! ### R3. `nlinarith` · closes a polynomial inequality over `ℝ` that follows from the hypotheses
It multiplies pairs of hypotheses (and squares) and then runs `linarith`. Plain `linarith` fails here:
`x ^ 2` is not linear in `x`. It reads only hypotheses of the form `a ≤ b`, `a < b`, `a = b` in the
context, never a `∀`, so instantiate first (R2). -/
example (x : ℝ) (hx : 2 ≤ x) : 2 * x ≤ x ^ 2 := by
  nlinarith

/-! ## Comparing two products term by term -/

/-! ### R4. `gcongr with i hi` on a product over `ℕ` · goal: `∏ ≤ ∏` → one factor
`∏ i ∈ s, f i` multiplies `f i` over every `i ∈ s`. A product is monotone only in nonnegative factors;
gcongr needs `0 ≤ f i` and proves it itself (with `positivity`) because every `ℕ` is `≥ 0`. -/
example {ι : Type} (s : Finset ι) (f g : ι → ℕ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  gcongr with i hi
  exact h i hi

/-! ## Membership in `range n` -/

/-! ### R5. `Finset.mem_range` · `m ∈ range n ↔ m < n`; `.mp` gives `m < n` · context gains `m < n`
`range n` is the finset `{0, 1, …, n - 1}`. `.mp` is the `→` direction of an `↔`. -/
example (m n : ℕ) (Q : Prop) (hm : m ∈ range n) (k : m < n → Q) : Q := by
  have h' : m < n := Finset.mem_range.mp hm
  exact k h'

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `gcongr` peels several layers at once: the sum, then the common factor `2 *` -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, 2 * g i := by
  gcongr with i hi
  exact h i hi

/-! ### W2. A product over `ℝ`: the side goal `∀ i ∈ s, 0 ≤ f i` is left to you, and comes first -/
example {ι : Type} (s : Finset ι) (f g : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  gcongr with i hi
  · exact h0
  · exact h i hi

/-! ### W3. Terms of different shapes: R1, then R2 to get a usable fact, then R3 -/
example {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, 2 * f i ≤ ∑ i ∈ s, f i ^ 2 := by
  gcongr with i hi
  have h2 := h i hi
  nlinarith

/-! ### W4. A product over `range m` with a `k < m` hypothesis: R4, then R2 fed by R5 -/
example (a b : ℕ → ℕ) (m : ℕ) (h : ∀ k < m, a k ≤ b k) :
    ∏ k ∈ range m, (a k + 1) ≤ ∏ k ∈ range m, (b k + 1) := by
  gcongr with k hk
  exact h k (Finset.mem_range.mp hk)

end E071Guide
