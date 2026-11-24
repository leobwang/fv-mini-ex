/- Guide for H033 (Wilson's theorem in a finite field).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (ℚ, ℕ, small explicit sets).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H033Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · algebra in a field: `x * x = 1` -/

/-! ### R1. `linear_combination h` · closes an equation that is `h` times a constant, up to `ring`
It checks `goal.lhs - goal.rhs - (h.lhs - h.rhs) = 0` with `ring`. `linear_combination c * h` scales `h`. -/
example {K : Type} [Field K] (a b c : K) (h : a * b = c) : a * b - c = 0 := by
  linear_combination h

/-! ### R2. `rcases mul_eq_zero.mp h with ha | hb` · goal list: one goal per factor that is zero
`mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0` (needs no zero divisors: true in a field). -/
example {K : Type} [Field K] (a b : K) (P : Prop) (h : a * b = 0) (h1 : a = 0 → P)
    (h2 : b = 0 → P) : P := by
  rcases mul_eq_zero.mp h with ha | hb
  · exact h1 ha
  · exact h2 hb

/-! ### R3. `sub_eq_zero` · `a - b = 0 ↔ a = b` · context: `h : a - b = 0` → `h : a = b` -/
example {K : Type} [Field K] (a b : K) (h : a - b = 0) : a = b := by
  rw [sub_eq_zero] at h
  exact h

/-! ### R4. `eq_neg_of_add_eq_zero_left` · `a + b = 0 → a = -b` · context gains `a = -b` -/
example {K : Type} [Field K] (a b : K) (h : a + b = 0) : a = -b := by
  have h' := eq_neg_of_add_eq_zero_left h
  exact h'

/-! ## Part 2 · products over a `Finset`, pairing by an involution -/

/-! ### R5. `Finset.prod_involution` · goal `∏ x ∈ s, f x = 1` → four goals about the pairing `g` -/
example {ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (g : ι → ι)
    (h1 : ∀ a ∈ s, f a * f (g a) = 1) (h2 : ∀ a ∈ s, f a ≠ 1 → g a ≠ a)
    (h3 : ∀ a ∈ s, g a ∈ s) (h4 : ∀ a ∈ s, g (g a) = a) : ∏ x ∈ s, f x = 1 := by
  refine Finset.prod_involution (fun a _ => g a) ?_ ?_ ?_ ?_
  exacts [h1, h2, h3, h4]

/-! ### R6. `Finset.mem_sdiff` · `a ∈ s \ t ↔ a ∈ s ∧ a ∉ t` · context -/
example {α : Type} [DecidableEq α] (s t : Finset α) (a : α) (P : Prop)
    (ha : a ∈ s \ t) (h : a ∈ s ∧ a ∉ t → P) : P := by
  rw [Finset.mem_sdiff] at ha
  exact h ha

/-! ### R7. `Finset.mem_erase` · `a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s` · context -/
example {α : Type} [DecidableEq α] (s : Finset α) (a b : α) (P : Prop)
    (ha : a ∈ s.erase b) (h : a ≠ b ∧ a ∈ s → P) : P := by
  rw [Finset.mem_erase] at ha
  exact h ha

/-! ### R8. `Finset.mem_univ`, `and_true` · `a ∈ Finset.univ` becomes `True`; `(p ∧ True) = p` · context
`Finset.mem_univ a : a ∈ Finset.univ` is a fact, not an `↔`: use it with `simp`, not `rw`. -/
example {α : Type} [Fintype α] (a : α) (p : Prop) (ha : p ∧ a ∈ Finset.univ) : p := by
  simp only [Finset.mem_univ] at ha
  rw [and_true] at ha
  exact ha

/-! ### R9. `Finset.mem_insert`, `Finset.mem_singleton` · `{b, c}` is `insert b {c}` · goal (or, with `at ha`, context)
`a ∈ insert b s ↔ a = b ∨ a ∈ s` and `a ∈ {c} ↔ a = c`. -/
example {α : Type} [DecidableEq α] (a b c : α) (P : Prop → Prop) (h : P (a = b ∨ a = c)) :
    P (a ∈ ({b, c} : Finset α)) := by
  rw [Finset.mem_insert]
  rw [Finset.mem_singleton]
  exact h

/-! ### R10. `not_or` · `¬(p ∨ q) ↔ ¬p ∧ ¬q` · context -/
example (p q : Prop) (hn : ¬(p ∨ q)) : ¬p ∧ ¬q := by
  rw [not_or] at hn
  exact hn

/-! ### R11. `mul_inv_cancel₀` · `a ≠ 0 → a * a⁻¹ = 1` · goal (`⁻¹` is the field inverse, `0⁻¹ = 0`) -/
example {K : Type} [Field K] (a : K) (ha : a ≠ 0) (P : K → Prop) (h : P 1) : P (a * a⁻¹) := by
  rw [mul_inv_cancel₀ ha]
  exact h

/-! ### R12. `calc` · prove `a = c` as a chain `a = b`, `b = c`, each step with its own proof -/
example {K : Type} [Field K] (a b c : K) (hab : a = b) (hbc : b = c) : a = c := by
  calc a = b := by rw [hab]
    _ = c := hbc

/-! ### R13. `refine fun h => hn ?_` · goal `¬B` → goal `A`, given `hn : ¬A`; context gains `h : B`
`¬B` is `B → False`; `hn ?_ : False` once you supply the `A`. -/
example (A B : Prop) (hn : ¬A) (hba : B → A) : ¬B := by
  refine fun h => hn ?_
  exact hba h

/-! ### R14. `inv_ne_zero` · `a ≠ 0 → a⁻¹ ≠ 0` · closes the goal -/
example {K : Type} [Field K] (a : K) (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  exact inv_ne_zero ha

/-! ### R15. `congrArg f h` · from `h : a = b` get `f a = f b` · context gains it -/
example {K : Type} [Field K] (a b : K) (h : a = b) : a⁻¹ = b⁻¹ := by
  have h' := congrArg (·⁻¹) h
  exact h'

/-! ### R16. `inv_inv` · `a⁻¹⁻¹ = a` · goal -/
example {K : Type} [Field K] (a : K) (P : K → Prop) (h : P a) : P a⁻¹⁻¹ := by
  rw [inv_inv]
  exact h

/-! ### R17. `simpa using h` · simplify both `h` and the goal, then close the goal with `h`
Here `simp` uses `inv_inv` (R16) and `inv_one : 1⁻¹ = 1`. -/
example {K : Type} [Field K] (a : K) (h : a⁻¹⁻¹ = 1⁻¹) : a = 1 := by
  simpa using h

/-! ## Part 3 · splitting a product: `s₂ = (s₂ \ s₁) ∪ s₁` -/

/-! ### R18. `intro x hx` on `s ⊆ t` · goal `s ⊆ t` → `x ∈ t`; context gains `x`, `hx : x ∈ s`
For `Finset`, `s ⊆ t` unfolds to `∀ ⦃x⦄, x ∈ s → x ∈ t`. -/
example {α : Type} (s t : Finset α) (h : ∀ x, x ∈ s → x ∈ t) : s ⊆ t := by
  intro x hx
  exact h x hx

/-! ### R19. `rcases hx with rfl | rfl` · goal list: one goal per case; context loses `x` and `hx`
`rfl` as a pattern substitutes the equation `x = 0` (resp. `x = 1`) everywhere. -/
example (x : ℕ) (P : ℕ → Prop) (h0 : P 0) (h1 : P 1) (hx : x = 0 ∨ x = 1) : P x := by
  rcases hx with rfl | rfl
  · exact h0
  · exact h1

/-! ### R20. `Finset.prod_sdiff` · `s₁ ⊆ s₂ → (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x`
Used right to left: `rw [← Finset.prod_sdiff hsub]` splits the product over `s₂`. -/
example {ι M : Type} [CommMonoid M] [DecidableEq ι] (s₁ s₂ : Finset ι) (f : ι → M)
    (hsub : s₁ ⊆ s₂) (P : M → Prop) (h : P ((∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x)) :
    P (∏ x ∈ s₂, f x) := by
  rw [← Finset.prod_sdiff hsub]
  exact h

/-! ### R21. `one_mul` · `1 * a = a` · goal -/
example {M : Type} [CommMonoid M] (a : M) (P : M → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ### R22. `by_cases h : p` · goal list: the goal twice, once with `h : p`, once with `h : ¬p` -/
example (p G : Prop) (h1 : p → G) (h2 : ¬p → G) : G := by
  by_cases h : p
  · exact h1 h
  · exact h2 h

/-! ### R23. `Finset.insert_eq_of_mem` · `a ∈ s → insert a s = s` · goal: `{a, a}` → `{a}`
`Finset.mem_singleton_self a : a ∈ {a}`. Plain `simp` does this step by itself. -/
example {α : Type} [DecidableEq α] (a : α) (P : Finset α → Prop) (h : P {a}) :
    P ({a, a} : Finset α) := by
  rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self a)]
  exact h

/-! ### R24. `Finset.prod_singleton` · `∏ x ∈ {a}, f x = f a` · goal -/
example {ι M : Type} [CommMonoid M] (f : ι → M) (a : ι) (P : M → Prop) (h : P (f a)) :
    P (∏ x ∈ {a}, f x) := by
  rw [Finset.prod_singleton]
  exact h

/-! ### R25. `Finset.prod_pair` · `a ≠ b → ∏ x ∈ {a, b}, f x = f a * f b` · goal -/
example {ι M : Type} [CommMonoid M] [DecidableEq ι] (f : ι → M) (a b : ι) (hab : a ≠ b)
    (P : M → Prop) (h : P (f a * f b)) : P (∏ x ∈ {a, b}, f x) := by
  rw [Finset.prod_pair hab]
  exact h

/-! ## Part 4 · primes and divisibility in ℕ -/

/-! ### R26. `Nat.prime_def` · `p.Prime ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p` · goal -/
example (p : ℕ) (h : 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p) : p.Prime := by
  rw [Nat.prime_def]
  exact h

/-! ### R27. `refine ⟨h, fun m hm => ?_⟩` · goal `A ∧ ∀ m, Q m → R m` → goal `R m`; context gains `m hm` -/
example (A : Prop) (Q R : ℕ → Prop) (ha : A) (hqr : ∀ m, Q m → R m) : A ∧ ∀ m, Q m → R m := by
  refine ⟨ha, fun m hm => ?_⟩
  exact hqr m hm

/-! ### R28. `by_contra hne` · goal `G` → goal `False`; context gains `hne : ¬G` -/
example (G : Prop) (h : ¬G → False) : G := by
  by_contra hne
  exact h hne

/-! ### R29. `push Not at h` · context: pushes `¬` inward (`¬(p ∨ q)` → `¬p ∧ ¬q`, `¬a = b` → `a ≠ b`) -/
example (a b c : ℕ) (h : ¬(a = b ∨ a = c)) : a ≠ b ∧ a ≠ c := by
  push Not at h
  exact h

/-! ### R30. `Nat.pos_of_dvd_of_pos` · `m ∣ n → 0 < n → 0 < m` · closes -/
example (m n : ℕ) (hm : m ∣ n) (hn : 0 < n) : 0 < m := by
  exact Nat.pos_of_dvd_of_pos hm hn

/-! ### R31. `omega` · closes linear arithmetic over ℕ and ℤ from the hypotheses (`-` truncates at 0) -/
example (n : ℕ) (h : 2 ≤ n) : 0 < n ∧ 1 ≤ n - 1 := by
  omega

/-! ### R32. `Nat.le_of_dvd` · `0 < n → m ∣ n → m ≤ n` · closes -/
example (m n : ℕ) (hn : 0 < n) (hm : m ∣ n) : m ≤ n := by
  exact Nat.le_of_dvd hn hm

/-! ### R33. `lt_of_le_of_ne` · `a ≤ b → a ≠ b → a < b` · closes -/
example (a b : ℕ) (hle : a ≤ b) (hne : a ≠ b) : a < b := by
  exact lt_of_le_of_ne hle hne

/-! ### R34. `Nat.dvd_factorial` · `0 < m → m ≤ n → m ∣ n.factorial` (`Nat.factorial n`, printed `n.factorial`) -/
example (m n : ℕ) (h0 : 0 < m) (hle : m ≤ n) : m ∣ n.factorial := by
  exact Nat.dvd_factorial h0 hle

/-! ### R35. `Dvd.dvd.trans` · `a ∣ b → b ∣ c → a ∣ c`; dot notation `hab.trans hbc` -/
example (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  exact hab.trans hbc

/-! ### R36. `Nat.dvd_add_right` · `a ∣ b → (a ∣ b + c ↔ a ∣ c)`; `.mp` turns `a ∣ b + c` into `a ∣ c` -/
example (a b c : ℕ) (hab : a ∣ b) (h : a ∣ b + c) : a ∣ c := by
  have h' := (Nat.dvd_add_right hab).mp h
  exact h'

/-! ### R37. `Nat.dvd_one` · `n ∣ 1 ↔ n = 1` · context -/
example (n : ℕ) (h : n ∣ 1) : n = 1 := by
  rw [Nat.dvd_one] at h
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Pairing by `x ↦ x⁻¹` on an explicit set of rationals: R5, R9, R19 -/
example : ∏ x ∈ ({2, 2⁻¹} : Finset ℚ), x = 1 := by
  refine Finset.prod_involution (fun x _ => x⁻¹) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> norm_num
  · intro a ha _ heq
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> norm_num at heq
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl <;> simp
  · intro a _
    exact inv_inv a

/-! ### W2. Membership in `(s.erase 0) \ {1, 2}`: R6, R7, R9, R10 in one `simp only`
`Finset.mem_range : a ∈ Finset.range n ↔ a < n` plays the role of R8 here. -/
example (a : ℕ) (ha : a ∈ ((Finset.range 10).erase 0) \ {1, 2}) : a ≠ 0 ∧ a ≠ 1 := by
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, not_or] at ha
  exact ⟨ha.1.1, ha.2.1⟩

/-! ### W3. Split off a sub-product: R20, then R25 on the pair -/
example : ∏ x ∈ ({1, 2, 3} : Finset ℕ), x = 6 := by
  have hsub : ({1, 2} : Finset ℕ) ⊆ {1, 2, 3} := by decide
  rw [← Finset.prod_sdiff hsub, Finset.prod_pair (by decide)]
  decide

/-! ### W4. A divisor `m ≤ 4` of `4.factorial + 1` is `1`: R34, R36, R37 -/
example (m : ℕ) (h0 : 0 < m) (hle : m ≤ 4) (h : m ∣ (4 : ℕ).factorial + 1) : m = 1 := by
  have h1 : m ∣ (4 : ℕ).factorial := Nat.dvd_factorial h0 hle
  have h2 : m ∣ 1 := (Nat.dvd_add_right h1).mp h
  exact Nat.dvd_one.mp h2

end H033Guide
