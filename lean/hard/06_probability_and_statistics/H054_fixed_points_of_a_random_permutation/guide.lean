/- Guide for H054 (Fixed points of a random permutation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a fair coin, elements of `Fin n`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H054Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · `card_apply_eq`: equal cardinalities from a bijection -/

/-! ### R1. `apply Finset.card_bij (fun a _ => f a)` · goal `s.card = t.card` → three goals
(maps into `t`, injective, surjective). The `_` is the unused proof of `a ∈ s`. -/
example {α β : Type} (s : Finset α) (t : Finset β) (f : α → β)
    (hmap : ∀ a ∈ s, f a ∈ t) (hinj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂)
    (hsurj : ∀ b ∈ t, ∃ a, ∃ (_ : a ∈ s), f a = b) : s.card = t.card := by
  apply Finset.card_bij (fun a _ => f a)
  exacts [hmap, hinj, hsurj]

/-! ### R2. `simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢` · context and goal:
`a ∈ {x | p x}` (a filtered `Finset.univ`) → `p a` -/
example {α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q] (a : α)
    (h : a ∈ Finset.univ.filter p) (hpq : p a → q a) : a ∈ Finset.univ.filter q := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  exact hpq h

/-! ### R3. `Equiv.Perm.mul_apply` · goal: `(σ * τ) x` → `σ (τ x)` (`*` is composition) -/
example {α : Type} (σ τ : Equiv.Perm α) (x : α) (P : α → Prop) (h : P (σ (τ x))) :
    P ((σ * τ) x) := by
  rw [Equiv.Perm.mul_apply]
  exact h

/-! ### R4. `Equiv.swap_apply_left` · goal: `Equiv.swap a b a` → `b` -/
example {α : Type} [DecidableEq α] (a b : α) (P : α → Prop) (h : P b) : P (Equiv.swap a b a) := by
  rw [Equiv.swap_apply_left]
  exact h

/-! ### R5. `Equiv.swap_apply_right` · goal: `Equiv.swap a b b` → `a` -/
example {α : Type} [DecidableEq α] (a b : α) (P : α → Prop) (h : P a) : P (Equiv.swap a b b) := by
  rw [Equiv.swap_apply_right]
  exact h

/-! ### R6. `mul_right_inj` · `a * b = a * c ↔ b = c` · context: cancel a common left factor -/
example {G : Type} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  rw [mul_right_inj] at h
  exact h

/-! ### R7. `simpa using h` · closes the goal when `simp` makes `h` and the goal the same -/
example {G : Type} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  simpa using h

/-! ### R8. `refine ⟨x, ?_, ?_⟩` · goal `∃ a, ∃ (_ : a ∈ s), f a = b` → two goals -/
example {α β : Type} (s : Finset α) (f : α → β) (b : β) (x : α) (hx : x ∈ s) (hfx : f x = b) :
    ∃ a, ∃ (_ : a ∈ s), f a = b := by
  refine ⟨x, ?_, ?_⟩
  exacts [hx, hfx]

/-! ### R9. `mul_assoc` · `a * b * c = a * (b * c)`; right to left: `rw [← mul_assoc]` -/
example {G : Type} [Monoid G] (a b c : G) (P : G → Prop) (h : P (a * b * c)) :
    P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R10. `Equiv.swap_mul_self` · goal: `Equiv.swap a b * Equiv.swap a b` → `1` -/
example {α : Type} [DecidableEq α] (a b : α) (P : Equiv.Perm α → Prop) (h : P 1) :
    P (Equiv.swap a b * Equiv.swap a b) := by
  rw [Equiv.swap_mul_self]
  exact h

/-! ### R11. `one_mul` · goal: `1 * a` → `a` -/
example {G : Type} [Monoid G] (a : G) (P : G → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ## Part 2 · `card_fix_mul`: count by fibres -/

/-! ### R12. `have h := Finset.card_eq_sum_card_fiberwise (f := f) hf` · context gains
`h : s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card` (split `s` by the value of `f`) -/
example {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (G : Prop)
    (g : s.card = ∑ b ∈ t, (s.filter fun a => f a = b).card → G) : G := by
  have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := t) (f := f) hf
  exact g h

/-! ### R13. `Finset.card_univ` · `Finset.univ.card = Fintype.card α` · here in the context -/
example {α : Type} [Fintype α] (m : ℕ) (h : (Finset.univ : Finset α).card = m) :
    Fintype.card α = m := by
  rw [Finset.card_univ] at h
  exact h

/-! ### R14. `Fintype.card_perm` · goal: `Fintype.card (Equiv.Perm α)` → `(Fintype.card α).factorial` -/
example {α : Type} [DecidableEq α] [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α).factorial) :
    P (Fintype.card (Equiv.Perm α)) := by
  rw [Fintype.card_perm]
  exact h

/-! ### R15. `Fintype.card_fin` · goal: `Fintype.card (Fin n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R16. `Finset.sum_congr rfl hfg` · goal: rewrite every summand with `hfg : ∀ x ∈ s, f x = g x` -/
example {α β : Type} [AddCommMonoid β] (s : Finset α) (f g : α → β) (hfg : ∀ x ∈ s, f x = g x)
    (P : β → Prop) (h : P (∑ x ∈ s, g x)) : P (∑ x ∈ s, f x) := by
  rw [Finset.sum_congr rfl hfg]
  exact h

/-! ### R17. `Finset.sum_const` · goal: a sum of a constant `c` → `s.card • c` -/
example {α β : Type} [AddCommMonoid β] (s : Finset α) (c : β) (P : β → Prop) (h : P (s.card • c)) :
    P (∑ _x ∈ s, c) := by
  rw [Finset.sum_const]
  exact h

/-! ### R18. `smul_eq_mul` · goal: `a • b` → `a * b` when both live in the same type -/
example {α : Type} [Mul α] (a b : α) (P : α → Prop) (h : P (a * b)) : P (a • b) := by
  rw [smul_eq_mul]
  exact h

/-! ### R19. `mul_comm` · goal: `a * b` → `b * a` (`rw` then tries `rfl`) -/
example {α : Type} [CommMonoid α] (a b : α) (P : α → Prop) (h : P (b * a)) : P (a * b) := by
  rw [mul_comm]
  exact h

/-! ## Part 3 · `sum_numFixed`: double counting -/

/-! ### R20. `Finset.card_filter` · goal: `{x ∈ s | p x}.card` → `∑ x ∈ s, if p x then 1 else 0` -/
example {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (P : ℕ → Prop)
    (h : P (∑ x ∈ s, if p x then 1 else 0)) : P (s.filter p).card := by
  rw [Finset.card_filter]
  exact h

/-! ### R21. `Nat.cast_sum` · goal: `↑(∑ x ∈ s, f x)` → `∑ x ∈ s, ↑(f x)` (cast into ℝ) -/
example {α : Type} (s : Finset α) (f : α → ℕ) (P : ℝ → Prop) (h : P (∑ x ∈ s, (f x : ℝ))) :
    P ((∑ x ∈ s, f x : ℕ) : ℝ) := by
  rw [Nat.cast_sum]
  exact h

/-! ### R22. `Nat.cast_ite`, `Nat.cast_one`, `Nat.cast_zero` · goal: push `↑` into an `if` -/
example (c : Prop) [Decidable c] (P : ℝ → Prop) (h : P (if c then 1 else 0)) :
    P ((if c then 1 else 0 : ℕ) : ℝ) := by
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact h

/-! ### R23. `Finset.sum_comm` · goal: swap the order of a double sum -/
example {α β γ : Type} [AddCommMonoid γ] (s : Finset α) (t : Finset β) (f : α → β → γ)
    (P : γ → Prop) (h : P (∑ y ∈ t, ∑ x ∈ s, f x y)) : P (∑ x ∈ s, ∑ y ∈ t, f x y) := by
  rw [Finset.sum_comm]
  exact h

/-! ## Part 4 · `expected_fixed_points`: integral → finite sum → arithmetic -/

/-! ### R24. `PMF.integral_eq_sum` · goal: `∫ a, f a ∂p.toMeasure` → `∑ a, (p a).toReal • f a` -/
example {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α)
    (f : α → ℝ) (P : ℝ → Prop) (h : P (∑ a, (p a).toReal • f a)) :
    P (∫ a, f a ∂p.toMeasure) := by
  rw [PMF.integral_eq_sum]
  exact h

/-! ### R25. `PMF.uniformOfFintype_apply` · goal: `PMF.uniformOfFintype α a` → `(↑(Fintype.card α))⁻¹` -/
example {α : Type} [Fintype α] [Nonempty α] (a : α) (P : ENNReal → Prop)
    (h : P (Fintype.card α : ENNReal)⁻¹) : P (PMF.uniformOfFintype α a) := by
  rw [PMF.uniformOfFintype_apply]
  exact h

/-! ### R26. `Finset.mul_sum` · `c * ∑ i ∈ s, f i = ∑ i ∈ s, c * f i`; right to left pulls `c` out -/
example {α : Type} (s : Finset α) (f : α → ℝ) (c : ℝ) (P : ℝ → Prop) (h : P (c * ∑ i ∈ s, f i)) :
    P (∑ i ∈ s, c * f i) := by
  rw [← Finset.mul_sum]
  exact h

/-! ### R27. `eq_div_iff hc` · `c ≠ 0 → (a = b / c ↔ a * c = b)` · goal: clear one division -/
example (a b c : ℝ) (hc : c ≠ 0) (h : a * c = b) : a = b / c := by
  rw [eq_div_iff hc]
  exact h

/-! ### R28. `positivity` · closes `0 < e`, `0 ≤ e`, `e ≠ 0`; for a variable it uses hypotheses
such as `hm : 1 ≤ m` -/
example (m : ℕ) (hm : 1 ≤ m) : (m : ℝ) ≠ 0 := by
  positivity

example (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity

/-! ### R29. `exact_mod_cast h` · closes a goal that is `h` with casts `↑` moved around -/
example (a b c : ℕ) (h : a * b = c) : (a : ℝ) * (b : ℝ) = (c : ℝ) := by
  exact_mod_cast h

/-! ### R30. `nsmul_eq_mul` · goal: `n • a` (with `n : ℕ`) → `↑n * a` -/
example (n : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! ### R31. `ENNReal.toReal_inv` · goal: `a⁻¹.toReal` → `a.toReal⁻¹` -/
example (a : ENNReal) (P : ℝ → Prop) (h : P a.toReal⁻¹) : P a⁻¹.toReal := by
  rw [ENNReal.toReal_inv]
  exact h

/-! ### R32. `ENNReal.toReal_natCast` · goal: `(↑n : ENNReal).toReal` → `(↑n : ℝ)` -/
example (n : ℕ) (P : ℝ → Prop) (h : P (n : ℝ)) : P (n : ENNReal).toReal := by
  rw [ENNReal.toReal_natCast]
  exact h

/-! ### R33. `field_simp` · clears denominators using the `≠ 0` facts in the context; may close the goal -/
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ * (a / b) * b = 1 := by
  field_simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Expectation on a fair coin: R24, R25 (+ `Fintype.card_bool`), R18, then `simp` finishes
`if b then …` on `b : Bool` prints as `if b = true then …`. -/
example : ∫ b, (if b then (1 : ℝ) else 0) ∂(PMF.uniformOfFintype Bool).toMeasure = 1 / 2 := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, smul_eq_mul]
  simp

/-! ### W2. A swap is a bijection between `{x | x = j}` and `{x | x = k}` inside `Fin n`: R1–R8 -/
example (n : ℕ) (j k : Fin n) :
    (Finset.univ.filter fun x : Fin n => x = j).card =
      (Finset.univ.filter fun x : Fin n => x = k).card := by
  apply Finset.card_bij (fun x _ => Equiv.swap j k x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simp [hx]
  · intro a _ b _ h
    simpa using h
  · intro y hy
    refine ⟨Equiv.swap j k y, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      simp [hy]
    · simp

end H054Guide
