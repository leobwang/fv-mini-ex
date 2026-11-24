/- Guide for M167 (Edges of the tight-binding band).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g`) in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other sets, other functions).
Assumed: Lean basics.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace M167Guide

/-! # Part R · Reference entries -/

/-! ## Exhibiting an allowed wavenumber -/

/-- A set defined like `T.QuantaWaveNumber`: the values `g n` for `n : Fin N`. -/
def Q (N : ℕ) (g : Fin N → ℝ) : Set ℝ := {x | ∃ n : Fin N, g n = x}

/-! ### R1. `refine ⟨⟨v, hv⟩, ?_⟩` · goal: `x ∈ {x | ∃ n : Fin N, g n = x}` → `g ⟨v, hv⟩ = x`
Membership in a set-builder set *is* the `∃`, even behind a `def` such as `Q` or
`T.QuantaWaveNumber`, so the anonymous constructor works directly. `⟨v, hv⟩ : Fin N` is the index
`v` together with a proof `hv : v < N`. -/
example (N : ℕ) (g : Fin N → ℝ) (x : ℝ) (v : ℕ) (hv : v < N) (h : g ⟨v, hv⟩ = x) : x ∈ Q N g := by
  refine ⟨⟨v, hv⟩, ?_⟩
  exact h

/-! ### R2. `NeZero.pos` · `[NeZero n] → 0 < n` · context gains `h : 0 < N`
`NeZero N` is a type-class fact "N ≠ 0"; physlib provides it for `T.N`. -/
example (N : ℕ) [NeZero N] (G : Prop) (g : 0 < N → G) : G := by
  have h := NeZero.pos N
  exact g h

/-! ### R3. `omega` · closes linear goals over `ℕ`/`ℤ`, including `/` and `%` by numerals -/
example (N : ℕ) (h : 0 < N) : N / 3 < N := by
  omega

example (N m : ℕ) (hm : N = m + m) : N / 2 = m := by
  omega

/-! ### R4. `simp only [sub_self, mul_zero]` · goal: `c * (↑↑⟨v, hv⟩ - ↑v)` → `0`
`↑↑⟨v, hv⟩` is the `Fin` index `⟨v, hv⟩` cast to `ℕ` and then to `ℝ`; it is `↑v` by definition, which
`simp` sees, so `sub_self : a - a = 0` applies. -/
example (N v : ℕ) (hv : v < N) (c : ℝ) (P : ℝ → Prop) (h : P 0) :
    P (c * (((⟨v, hv⟩ : Fin N) : ℕ) - (v : ℝ))) := by
  simp only [sub_self, mul_zero]
  exact h

/-! ## Least and greatest elements of a range -/

/-! ### R5. `IsLeast s a` is `a ∈ s ∧ a ∈ lowerBounds s` · `refine ⟨?_, ?_⟩` · goal → two goals -/
example (s : Set ℝ) (a : ℝ) (h1 : a ∈ s) (h2 : a ∈ lowerBounds s) : IsLeast s a := by
  refine ⟨?_, ?_⟩
  exacts [h1, h2]

/-! ### R6. `Set.range f` membership · `refine ⟨⟨x, hx⟩, ?_⟩` · goal: `b ∈ Set.range f` → `f ⟨x, hx⟩ = b`
Here `f` is defined on the subtype `↑S` (elements of the set `S`), so its argument is a pair
`⟨x, hx⟩` with `hx : x ∈ S`. -/
example (S : Set ℝ) (f : S → ℝ) (x b : ℝ) (hx : x ∈ S) (h : f ⟨x, hx⟩ = b) : b ∈ Set.range f := by
  refine ⟨⟨x, hx⟩, ?_⟩
  exact h

/-! ### R7. `unfold TightBindingChain.energyEigenvalue` · goal: `T.energyEigenvalue k` → its formula -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : ℝ → Prop)
    (h : P (T.E0 - 2 * T.t * Real.cos (k * T.a))) : P (T.energyEigenvalue k) := by
  unfold TightBindingChain.energyEigenvalue
  exact h

/-! ### R8. `zero_mul`, `Real.cos_zero` · goal: `cos (↑⟨0, h0⟩ * a)` → `cos 0` → `1`
`↑⟨0, h0⟩` (a subtype element cast back to `ℝ`) is `0` by definition, so `zero_mul : 0 * a = 0` fires. -/
example (S : Set ℝ) (h0 : (0 : ℝ) ∈ S) (a : ℝ) (P : ℝ → Prop) (h : P 1) :
    P (Real.cos ((⟨0, h0⟩ : S) * a)) := by
  simp only [zero_mul]
  rw [Real.cos_zero]
  exact h

/-! ### R9. `rintro _ ⟨k, rfl⟩` · goal: `a ∈ lowerBounds (Set.range f)` → `a ≤ f k`; context gains `k`
`a ∈ lowerBounds s` is `∀ ⦃y⦄, y ∈ s → a ≤ y`; `rfl` replaces `y` by `f k` everywhere. -/
example (S : Set ℝ) (f : S → ℝ) (a : ℝ) (h : ∀ k, a ≤ f k) : a ∈ lowerBounds (Set.range f) := by
  rintro _ ⟨k, rfl⟩
  exact h k

/-! ### R10. `Real.cos_le_one` · `cos x ≤ 1` · context gains `h : Real.cos x ≤ 1` -/
example (x : ℝ) (G : Prop) (g : Real.cos x ≤ 1 → G) : G := by
  have h := Real.cos_le_one x
  exact g h

/-! ### R11. `nlinarith` · closes a linear-arithmetic goal that needs a product of two hypotheses -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 1) : x * y ≤ x := by
  nlinarith

/-! ## Even `N`, casts and fractions -/

/-! ### R12. `obtain ⟨m, hm⟩ := hN` · context: `hN : Even N` → `m : ℕ`, `hm : N = m + m` -/
example (N : ℕ) (hN : Even N) (G : Prop) (g : ∀ m, N = m + m → G) : G := by
  obtain ⟨m, hm⟩ := hN
  exact g m hm

/-! ### R13. `T.a_pos` · a field of the structure: context gains `ha : 0 < T.a` -/
example (T : TightBindingChain) (G : Prop) (g : 0 < T.a → G) : G := by
  have ha := T.a_pos
  exact g ha

/-! ### R14. `exact_mod_cast h` · closes `(0 : ℝ) < ↑m` from `h : 0 < m` in `ℕ` -/
example (m : ℕ) (h : 0 < m) : (0 : ℝ) < m := by
  exact_mod_cast h

/-! ### R15. `push_cast` · goal: the cast `↑(m + m)` moves inward → `↑m + ↑m` -/
example (m : ℕ) (P : ℝ → Prop) (h : P (↑m + ↑m)) : P ((m + m : ℕ) : ℝ) := by
  push_cast
  exact h

/-! ### R16. `simp` on `c * (↑↑⟨0, hN⟩ - ↑m) = -d` · goal → `c * ↑m = d`
`simp` turns the index `0` into `0`, then uses `zero_sub`, `mul_neg` and `neg_inj : -a = -b ↔ a = b`. -/
example (N m : ℕ) (hN : 0 < N) (c d : ℝ) (h : c * m = d) :
    c * (((⟨0, hN⟩ : Fin N) : ℕ) - (m : ℝ)) = -d := by
  simp
  exact h

/-! ### R17. `field_simp` · clears denominators (it needs `a ≠ 0` or `0 < a` facts in the context) -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 3 / (a * (3 * b)) * b = 1 / a := by
  field_simp

/-! ### R18. `IsGreatest s a` is `a ∈ s ∧ a ∈ upperBounds s` · `refine ⟨?_, ?_⟩` · goal → two goals -/
example (s : Set ℝ) (a : ℝ) (h1 : a ∈ s) (h2 : a ∈ upperBounds s) : IsGreatest s a := by
  refine ⟨?_, ?_⟩
  exacts [h1, h2]

/-! ## The energy at `k = -π/a` -/

/-! ### R19. `neg_mul` · `-a * b = -(a * b)` · goal -/
example {α : Type} [Ring α] (a b : α) (P : α → Prop) (h : P (-(a * b))) : P (-a * b) := by
  rw [neg_mul]
  exact h

/-! ### R20. `LT.lt.ne'` · `0 < a → a ≠ 0`, written `ha.ne'` · context gains `h : a ≠ 0` -/
example (a : ℝ) (ha : 0 < a) (G : Prop) (g : a ≠ 0 → G) : G := by
  have h := ha.ne'
  exact g h

/-! ### R21. `div_mul_cancel₀` · `b ≠ 0 → a / b * b = a` · goal; write `rw [div_mul_cancel₀ _ hb]` -/
example {α : Type} [GroupWithZero α] (a b : α) (hb : b ≠ 0) (P : α → Prop) (h : P a) :
    P (a / b * b) := by
  rw [div_mul_cancel₀ _ hb]
  exact h

/-! ### R22. `Real.cos_neg` · `cos (-x) = cos x` · goal -/
example (x : ℝ) (P : ℝ → Prop) (h : P (Real.cos x)) : P (Real.cos (-x)) := by
  rw [Real.cos_neg]
  exact h

/-! ### R23. `Real.cos_pi` · `cos π = -1` · goal -/
example (P : ℝ → Prop) (h : P (-1)) : P (Real.cos Real.pi) := by
  rw [Real.cos_pi]
  exact h

/-! ### R24. `rintro _ ⟨k, rfl⟩` · goal: `a ∈ upperBounds (Set.range f)` → `f k ≤ a`; context gains `k` -/
example (S : Set ℝ) (f : S → ℝ) (a : ℝ) (h : ∀ k, f k ≤ a) : a ∈ upperBounds (Set.range f) := by
  rintro _ ⟨k, rfl⟩
  exact h k

/-! ### R25. `Real.neg_one_le_cos` · `-1 ≤ cos x` · context gains `h : -1 ≤ Real.cos x` -/
example (x : ℝ) (G : Prop) (g : -1 ≤ Real.cos x → G) : G := by
  have h := Real.neg_one_le_cos x
  exact g h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A least element of a range on `ℝ`: R5, R6, R9, R10, then `linarith` -/
example : IsLeast (Set.range fun x : ℝ => 3 - Real.cos x) 2 := by
  refine ⟨⟨0, by simp; norm_num⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := Real.cos_le_one x
  simp only
  linarith

/-! ### W2. An index with ℕ division, for an even `N`: R12, R1, R3, R15, R16 -/
example (N : ℕ) [NeZero N] (hN : Even N) :
    -((N : ℝ) / 2) ∈ Q N (fun n => ((n : ℕ) : ℝ) - (N / 2 : ℕ)) := by
  obtain ⟨m, hm⟩ := hN
  refine ⟨⟨0, NeZero.pos N⟩, ?_⟩
  have h2 : N / 2 = m := by omega
  have hNr : (N : ℝ) = 2 * m := by rw [hm]; push_cast; ring
  rw [h2, hNr]
  simp

/-! ### W3. A cosine at `-π/b · b`: R20, R19, R21, R22, R23 -/
example (b : ℝ) (hb : 0 < b) : 2 * Real.cos (-(Real.pi / b) * b) + 2 = 0 := by
  rw [neg_mul, div_mul_cancel₀ _ hb.ne', Real.cos_neg, Real.cos_pi]
  ring

end M167Guide
