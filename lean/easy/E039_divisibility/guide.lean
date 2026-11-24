/- Guide for E039 (Divisibility).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `g` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033): `obtain` on `∃` (E007, E030), `refine`, `exact`, `apply`, `have`.
-/
import Mathlib

namespace E039Guide

/-! # Part R · Reference entries -/

/-! ## Using a hypothesis `h : a ∣ b`
`a ∣ b` (typed `\mid`) is Mathlib's divisibility. In ℕ, ℤ and every monoid it is *defined* as
`∃ c, b = a * c`, so the `∃` tools from E007 work on it directly: no unfolding step is needed. -/

/-! ### R1. `obtain ⟨k, hk⟩ := h` · context: `h : a ∣ b` → `k : α`, `hk : b = a * k`
`k` is the cofactor. Note the order: `b = a * k`, the multiple on the left. -/
example {α : Type} [Monoid α] (a b : α) (h : a ∣ b) (P : Prop) (g : ∀ k, b = a * k → P) : P := by
  obtain ⟨k, hk⟩ := h
  exact g k hk

/-! ### R2. `obtain ⟨k, rfl⟩ := h` · context loses `b` and `h`; `b` is replaced by `a * k` everywhere
Works because `b` is a local variable: `rfl` substitutes the equation `b = a * k` into the goal and
into every other hypothesis (a later `h2 : b ∣ c` becomes `h2 : a * k ∣ c`). -/
example {α : Type} [Monoid α] (a b : α) (h : a ∣ b) (P : α → Prop) (g : ∀ k, P (a * k)) : P b := by
  obtain ⟨k, rfl⟩ := h
  exact g k

/-! ## Proving a goal `a ∣ b` -/

/-! ### R3. `refine ⟨k, ?_⟩` · goal `a ∣ b` → `b = a * k`
You choose the cofactor `k`; what remains is an equation. `exact ⟨k, by ring⟩` does R3 and R4 in one
term. (`Dvd.intro k h` is the same with the equation flipped: `h : a * k = b`.) -/
example {α : Type} [Monoid α] (a b k : α) (g : b = a * k) : a ∣ b := by
  refine ⟨k, ?_⟩
  exact g

/-! ### R4. `ring` · closes an identity of commutative (semi)rings
It normalises both sides as polynomials: reassociates, commutes, distributes, expands `(x * y) ^ n`.
It uses no hypotheses. ℕ, ℤ, ℚ, ℝ, ℂ are commutative semirings. -/
example {α : Type} [CommSemiring α] (x y z : α) : x * y * z = x * (z * y) := by
  ring

example {α : Type} [CommSemiring α] (x y : α) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  ring

/-! ## Library lemmas: build `a ∣ …` from `a ∣ b` without unpacking -/

/-! ### R5. `dvd_mul_of_dvd_right` · `a ∣ b → ∀ c, a ∣ c * b` · context gains `h : a ∣ c * b`
The name says where `b` sits in the product: on the right. The factor `c` is an explicit argument.
(Its twin `dvd_mul_of_dvd_left : a ∣ b → ∀ c, a ∣ b * c` puts `b` on the left.) -/
example {α : Type} [CommSemigroup α] (a b c : α) (hb : a ∣ b) (P : Prop) (g : a ∣ c * b → P) :
    P := by
  have h := dvd_mul_of_dvd_right hb c
  exact g h

/-! ### R6. `dvd_sub` · `a ∣ b → a ∣ c → a ∣ b - c` · `apply dvd_sub`: goal → two goals
`[Ring α]`: α has `+`, `*` and a true subtraction (ℤ, ℚ, ℝ, ℂ; not ℕ). Its sibling
`dvd_add : a ∣ b → a ∣ c → a ∣ b + c` works in ℕ too. -/
example {α : Type} [Ring α] (a b c : α) (hb : a ∣ b) (hc : a ∣ c) : a ∣ b - c := by
  apply dvd_sub
  exacts [hb, hc]

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Unpack two hypotheses, give a cofactor, finish by `ring`: R2, R2, R3, R4 -/
example (a b c d : ℕ) (h1 : a ∣ b) (h2 : c ∣ d) : a * c ∣ b * d := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := h2
  refine ⟨k * m, ?_⟩
  ring

/-! ### W2. Lemma terms only, no unpacking: R5 inside `dvd_add` (the `+` sibling of R6) -/
example (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ 5 * b + 4 * c := by
  exact dvd_add (dvd_mul_of_dvd_right h1 5) (dvd_mul_of_dvd_right h2 4)

end E039Guide
