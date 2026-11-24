/- Guide for M061 (Chinese remainder theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal". A hypothesis `h` (or `g`, `k`) in an entry is only there to
finish the example; it shows what the goal or context became.
Part W: worked combinations on objects that are NOT the exercise's (moduli 3 and 5, multiplying a
congruence by a constant).
Assumed: Lean basics.
-/
import Mathlib

namespace M061Guide

/-! # Part R · Reference entries -/

/-! ## Unpacking and splitting -/

/-! ### R1. `obtain ⟨u, v, huv⟩ := h` (`h : IsCoprime m n`) · context: `h` → `u v` and `huv`
`IsCoprime m n` is defined as `∃ u v, u * m + v * n = 1`, so it unpacks like any `∃`. -/
example {R : Type} [CommSemiring R] (m n : R) (h : IsCoprime m n) (G : Prop)
    (k : ∀ u v : R, u * m + v * n = 1 → G) : G := by
  obtain ⟨u, v, huv⟩ := h
  exact k u v huv

/-! ### R2. `refine ⟨x₀, ?_, ?_⟩` · goal `∃ x, P x ∧ Q x` → two goals `P x₀`, `Q x₀` -/
example {α : Type} (P Q : α → Prop) (x₀ : α) (hp : P x₀) (hq : Q x₀) : ∃ x, P x ∧ Q x := by
  refine ⟨x₀, ?_, ?_⟩
  exacts [hp, hq]

/-! ## Congruences as divisibility -/

/-! ### R3. `rw [Int.modEq_iff_dvd]` · goal: `a ≡ b [ZMOD n]` → `n ∣ b - a` (right side minus left) -/
example (n a b : ℤ) (h : n ∣ b - a) : a ≡ b [ZMOD n] := by
  rw [Int.modEq_iff_dvd]
  exact h

/-! ### R4. `refine ⟨c, ?_⟩` on `a ∣ k` · goal: divisibility → the equation `k = a * c`
`a ∣ k` is defined as `∃ c, k = a * c`; you supply the witness `c`. -/
example {R : Type} [CommRing R] (a k c : R) (h : k = a * c) : a ∣ k := by
  refine ⟨c, ?_⟩
  exact h

/-! ### R5. `linear_combination e₁ * h₁ + e₂ * h₂` · closes an equation that is a linear
combination of hypotheses: `(lhs - rhs) - Σ eᵢ * (lhsᵢ - rhsᵢ)` must be `0` by `ring`. -/
example {R : Type} [CommRing R] (a b c d : R) (h₁ : a = b) (h₂ : c = d) :
    a + 2 * c = b + 2 * d := by
  linear_combination h₁ + 2 * h₂

/-! ### R6. `rw [Int.modEq_iff_dvd] at *` · goal AND context: every `≡ [ZMOD _]` → `∣` -/
example (m k x y : ℤ) (hm : x ≡ y [ZMOD m]) (g : m ∣ y - x → k ∣ y - x) : x ≡ y [ZMOD k] := by
  rw [Int.modEq_iff_dvd] at *
  exact g hm

/-! ### R7. `obtain ⟨s, hs⟩ := hdvd` (`hdvd : a ∣ k`) · context: `hdvd` → `s` and `hs : k = a * s` -/
example {R : Type} [CommRing R] (a k : R) (hdvd : a ∣ k) (G : Prop) (g : ∀ s, k = a * s → G) :
    G := by
  obtain ⟨s, hs⟩ := hdvd
  exact g s hs

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A concrete solution of two congruences: R2, then R3 on both goals with `<;>`, then R4 -/
example : ∃ x : ℤ, x ≡ 2 [ZMOD 3] ∧ x ≡ 3 [ZMOD 5] := by
  refine ⟨8, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd]
  · exact ⟨-2, by norm_num⟩
  · exact ⟨-1, by norm_num⟩

/-! ### W2. Two divisibilities → divisibility by the product, with `2 * 3 + (-1) * 5 = 1`: R7, R4, R5
`a = a * (2 * 3 - 5)`; substitute `a = 5 * t` in the first term and `a = 3 * s` in the second. -/
example (a : ℤ) (h3 : 3 ∣ a) (h5 : 5 ∣ a) : 15 ∣ a := by
  obtain ⟨s, hs⟩ := h3
  obtain ⟨t, ht⟩ := h5
  exact ⟨2 * t - s, by linear_combination (-5) * hs + 6 * ht⟩

/-! ### W3. Multiply a congruence by `k`: R6, R7, R4, R5 one step at a time -/
example (m a b k : ℤ) (h : a ≡ b [ZMOD m]) : k * a ≡ k * b [ZMOD m] := by
  rw [Int.modEq_iff_dvd] at *
  obtain ⟨s, hs⟩ := h
  refine ⟨k * s, ?_⟩
  linear_combination k * hs

end M061Guide
