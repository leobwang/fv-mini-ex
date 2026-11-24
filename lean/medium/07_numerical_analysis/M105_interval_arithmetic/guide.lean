/- Guide for M105 (Interval arithmetic).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a segment type `Seg`, negation,
other `min`/`max` shapes).
Assumed: Lean basics.
-/
import Mathlib

namespace M105Guide

/-- A stand-in structure for the examples: two real fields, like the exercise's intervals. -/
structure Seg where
  lo : ℝ
  hi : ℝ

/-- Membership in a segment: a `def` whose body is a conjunction. -/
def Seg.In (x : ℝ) (S : Seg) : Prop := S.lo ≤ x ∧ x ≤ S.hi

/-- A structure-valued `def`: shift both endpoints by `c`. -/
def Seg.shift (S : Seg) (c : ℝ) : Seg := ⟨S.lo + c, S.hi + c⟩

/-! # Part R · Reference entries -/

/-! ## Taking hypotheses apart, splitting goals, unfolding -/

/-! ### R1. `obtain ⟨h1, h2⟩ := hx` · context: `hx : A ∧ B` (even behind a `def`) → `h1 : A`, `h2 : B` -/
example (x : ℝ) (S : Seg) (P : Prop) (h : S.lo ≤ x → x ≤ S.hi → P) (hx : Seg.In x S) : P := by
  obtain ⟨h1, h2⟩ := hx
  exact h h1 h2

/-! ### R2. `refine ⟨?_, ?_⟩` · goal list: a goal `A ∧ B` (even behind a `def`) → goals `A`, `B`
`exact ⟨p, q⟩` does the same in one step when you already have the two proofs `p`, `q`. -/
example (x : ℝ) (S : Seg) (h1 : S.lo ≤ x) (h2 : x ≤ S.hi) : Seg.In x S := by
  refine ⟨?_, ?_⟩
  exacts [h1, h2]

/-! ### R3. `simp only [Seg.shift]` · goal: unfold a structure-valued `def` and read off a field
`(S.shift c).lo` is the field `lo` of `⟨S.lo + c, S.hi + c⟩`, which is `S.lo + c`. -/
example (S : Seg) (c : ℝ) (P : ℝ → Prop) (h : P (S.lo + c)) : P (S.shift c).lo := by
  simp only [Seg.shift]
  exact h

/-! ### R4. `linarith` · closes a linear (in)equality that follows from the hypotheses by adding them -/
example (a c x y : ℝ) (h1 : a ≤ x) (h3 : c ≤ y) : a + c ≤ x + y := by
  linarith

/-! ## Order facts: case split, transitivity, `min`, `max`, products -/

/-! ### R5. `rcases le_total a b with h | h` · goal list: one goal → two, with `h : a ≤ b` / `h : b ≤ a`
`le_total a b : a ≤ b ∨ b ≤ a` holds in every linear order (ℝ, ℚ, ℤ, ℕ). -/
example {α : Type} [LinearOrder α] (a b : α) (P : Prop) (h1 : a ≤ b → P) (h2 : b ≤ a → P) : P := by
  rcases le_total a b with h | h
  exacts [h1 h, h2 h]

/-! ### R6. `refine le_trans ?_ hbc` · goal: `a ≤ c` → `a ≤ b`, given `hbc : b ≤ c`
`le_trans : a ≤ b → b ≤ c → a ≤ c`. Fill the side you know, leave `?_` for the other. -/
example {α : Type} [Preorder α] (a b c : α) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  refine le_trans ?_ hbc
  exact hab

/-! ### R7. `min_le_left a b : min a b ≤ a`, `min_le_right a b : min a b ≤ b` · closes the goal -/
example {α : Type} [LinearOrder α] (a b : α) : min a b ≤ a ∧ min a b ≤ b := by
  refine ⟨?_, ?_⟩
  exact min_le_left a b
  exact min_le_right a b

/-! ### R8. `le_max_left a b : a ≤ max a b`, `le_max_right a b : b ≤ max a b` · closes the goal -/
example {α : Type} [LinearOrder α] (a b : α) : a ≤ max a b ∧ b ≤ max a b := by
  refine ⟨?_, ?_⟩
  exact le_max_left a b
  exact le_max_right a b

/-! ### R9. `nlinarith` · closes an inequality between products, using products of hypotheses
Here it multiplies `0 ≤ x - a` by `0 ≤ y`. With `hy : y ≤ 0` the inequality flips. -/
example (a x y : ℝ) (h : a ≤ x) (hy : 0 ≤ y) : a * y ≤ x * y := by
  nlinarith

example (a x y : ℝ) (h : a ≤ x) (hy : y ≤ 0) : x * y ≤ a * y := by
  nlinarith

/-! ## Using a lemma you proved, and assembling `min`/`max` bounds -/

/-- A two-part lemma to instantiate in R10 (any lemma `L … : A ∧ B` works the same way). -/
theorem addBoth (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c ∧ c + a ≤ c + b :=
  ⟨by linarith, by linarith⟩

/-! ### R10. `obtain ⟨k1, k2⟩ := addBoth p q r hpq` · context gains both halves, at your arguments
The arguments replace the lemma's variables in order: `a := p`, `b := q`, `c := r`. -/
example (p q r : ℝ) (hpq : p ≤ q) (P : Prop) (h : p + r ≤ q + r → r + p ≤ r + q → P) : P := by
  obtain ⟨k1, k2⟩ := addBoth p q r hpq
  exact h k1 k2

/-! ### R11. `simp only [mul_comm _ a] at h` · context: every product `? * a` in `h` → `a * ?`
`mul_comm x y : x * y = y * x`; `mul_comm _ a` fixes the right factor `a`. -/
example (a b c : ℝ) (h : c ≤ b * a) (P : ℝ → Prop) (k : c ≤ a * b → P c) : P c := by
  simp only [mul_comm _ a] at h
  exact k h

/-! ### R12. `refine le_min ?_ ?_` · goal list: `a ≤ min b c` → `a ≤ b`, `a ≤ c`
`le_min : a ≤ b → a ≤ c → a ≤ min b c`. -/
example {α : Type} [LinearOrder α] (a b c : α) (hb : a ≤ b) (hc : a ≤ c) : a ≤ min b c := by
  refine le_min ?_ ?_
  exacts [hb, hc]

/-! ### R13. `refine max_le ?_ ?_` · goal list: `max a b ≤ c` → `a ≤ c`, `b ≤ c`
`max_le : a ≤ c → b ≤ c → max a b ≤ c`. -/
example {α : Type} [LinearOrder α] (a b c : α) (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  refine max_le ?_ ?_
  exacts [ha, hb]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- Negating a segment swaps and negates its endpoints. -/
def Seg.neg (S : Seg) : Seg := ⟨-S.hi, -S.lo⟩

/-! ### W1. Soundness of negation: R1, R2, then R3 and R4 in each goal -/
example (x : ℝ) (S : Seg) (hx : Seg.In x S) : Seg.In (-x) S.neg := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [Seg.neg]
    linarith
  · simp only [Seg.neg]
    linarith

/-! ### W2. A sign split, then a bound through `max`: R5, then R6 with R8 in each case -/
example (y : ℝ) : 0 ≤ max y (-y) := by
  rcases le_total 0 y with hy | hy
  · exact le_trans hy (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)

/-! ### W3. Lower bound out of a nested `min`: R6 twice, then R7 twice -/
example (a b c t : ℝ) (hb : b ≤ t) : min (min a b) c ≤ t := by
  refine le_trans ?_ hb
  refine le_trans (min_le_left _ _) ?_
  exact min_le_right _ _

/-! ### W4. Lower bound into a nested `min`: R12 twice -/
example (a b c t : ℝ) (ha : t ≤ a) (hb : t ≤ b) (hc : t ≤ c) : t ≤ min a (min b c) := by
  refine le_min ha ?_
  exact le_min hb hc

/-! ### W5. Flip products with R11, then finish with R4 -/
example (s u v : ℝ) (h1 : 0 ≤ u * s) (h2 : u * s ≤ v * s) : 0 ≤ s * v := by
  simp only [mul_comm _ s] at h1 h2
  linarith

end M105Guide
