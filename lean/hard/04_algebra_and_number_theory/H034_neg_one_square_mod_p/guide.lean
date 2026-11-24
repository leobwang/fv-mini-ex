/- Guide for H034 (When is −1 a square mod p?).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G` is an arbitrary goal and `g` the fact that finishes it, when the step changes only the context.
Part W: worked combinations on objects that are NOT the exercise's (ZMod 7, ZMod 5).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H034Guide

open Finset

/-! # Part R · Reference entries -/

/-! ## Part 1 · factorials as products, casts into `ZMod` -/

/-! ### R1. `Nat.ascFactorial_eq_prod_range` · goal: `∏ i ∈ range k, (n + i)` → `n.ascFactorial k`
Used right to left: `rw [← Nat.ascFactorial_eq_prod_range]`. -/
example (n k : ℕ) (P : ℕ → Prop) (h : P (n.ascFactorial k)) : P (∏ i ∈ range k, (n + i)) := by
  rw [← Nat.ascFactorial_eq_prod_range]
  exact h

/-! ### R2. `Nat.factorial_mul_ascFactorial` · goal: `n ! * (n + 1).ascFactorial k` → `(n + k)!` -/
example (n k : ℕ) (P : ℕ → Prop) (h : P (n + k).factorial) :
    P (n.factorial * (n + 1).ascFactorial k) := by
  rw [Nat.factorial_mul_ascFactorial]
  exact h

/-! ### R3. `two_mul` · goal: `2 * a` → `a + a` -/
example {α : Type} [NonAssocSemiring α] (a : α) (P : α → Prop) (h : P (a + a)) : P (2 * a) := by
  rw [two_mul]
  exact h

/-! ### R4. `Finset.mem_range` with `at hi` · context: `hi : i ∈ range n` → `hi : i < n` -/
example (n i : ℕ) (hi : i ∈ range n) (G : Prop) (g : i < n → G) : G := by
  rw [Finset.mem_range] at hi
  exact g hi

/-! ### R5. `eq_neg_iff_add_eq_zero` · goal: `a = -b` → `a + b = 0` -/
example {A : Type} [AddGroup A] (a b : A) (h : a + b = 0) : a = -b := by
  rw [eq_neg_iff_add_eq_zero]
  exact h

/-! ### R6. `Nat.cast_add` · `↑(m + n) = ↑m + ↑n`; right to left moves `+` inside the cast -/
example {R : Type} [AddMonoidWithOne R] (m n : ℕ) (P : R → Prop) (h : P ((m + n : ℕ) : R)) :
    P ((m : R) + (n : R)) := by
  rw [← Nat.cast_add]
  exact h

/-! ### R7. `ZMod.natCast_eq_zero_iff` · goal: `(↑a : ZMod b) = 0` → `b ∣ a` -/
example (a b : ℕ) (h : b ∣ a) : ((a : ℕ) : ZMod b) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact h

/-! ### R8. `rw [show e₁ = e₂ by omega]` · goal: replace a `ℕ` expression by an equal one
`omega` proves the equation (it knows truncated `-`); `rw` then closes a goal `x ∣ x` or `x = x`
by itself. -/
example (a b : ℕ) (hab : a ≤ b) (P : ℕ → Prop) (h : P b) : P (a + (b - a)) := by
  rw [show a + (b - a) = b by omega]
  exact h

/-! ### R9. `Finset.prod_range_add_one_eq_factorial` · `∏ i ∈ range n, (i + 1) = n !`
Used right to left: goal `n !` → the product. -/
example (n : ℕ) (P : ℕ → Prop) (h : P (∏ i ∈ range n, (i + 1))) : P n.factorial := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  exact h

/-! ### R10. `Finset.prod_range_reflect` · `∏ j ∈ range n, f (n - 1 - j) = ∏ j ∈ range n, f j`
Used right to left: the product is re-indexed backwards, `j ↦ n - 1 - j`. -/
example {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∏ j ∈ range n, f (n - 1 - j))) : P (∏ j ∈ range n, f j) := by
  rw [← Finset.prod_range_reflect]
  exact h

/-! ### R11. `Finset.prod_congr` · goal: equal products → equal factors, one per element -/
example {M : Type} [CommMonoid M] (s : Finset ℕ) (f g : ℕ → M) (h : ∀ x ∈ s, f x = g x) :
    ∏ x ∈ s, f x = ∏ x ∈ s, g x := by
  refine Finset.prod_congr rfl ?_
  exact h

/-! ### R12. `Nat.cast_mul` · goal: `↑(m * n)` → `↑m * ↑n` -/
example {R : Type} [NonAssocSemiring R] (m n : ℕ) (P : R → Prop) (h : P ((m : R) * (n : R))) :
    P ((m * n : ℕ) : R) := by
  rw [Nat.cast_mul]
  exact h

/-! ### R13. `Nat.cast_prod` · goal: `↑(∏ i ∈ s, f i)` → `∏ i ∈ s, ↑(f i)`; `←` folds it back -/
example {R : Type} [CommSemiring R] (s : Finset ℕ) (f : ℕ → ℕ) (P : R → Prop)
    (h : P (∏ i ∈ s, (f i : R))) : P ((∏ i ∈ s, f i : ℕ) : R) := by
  rw [Nat.cast_prod]
  exact h

/-! ### R14. `rw [Finset.prod_congr rfl h]` · goal: rewrite every factor of a product with `h` -/
example {M : Type} [CommMonoid M] (s : Finset ℕ) (f g : ℕ → M) (h : ∀ x ∈ s, f x = g x)
    (P : M → Prop) (hg : P (∏ x ∈ s, g x)) : P (∏ x ∈ s, f x) := by
  rw [Finset.prod_congr rfl h]
  exact hg

/-! ### R15. `Finset.prod_neg` · goal: `∏ x ∈ s, -f x` → `(-1) ^ #s * ∏ x ∈ s, f x` -/
example {M : Type} [CommRing M] (s : Finset ℕ) (f : ℕ → M) (P : M → Prop)
    (h : P ((-1) ^ s.card * ∏ x ∈ s, f x)) : P (∏ x ∈ s, -f x) := by
  rw [Finset.prod_neg]
  exact h

/-! ### R16. `Finset.card_range` · goal: `#(range n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (range n).card := by
  rw [Finset.card_range]
  exact h

/-! ## Part 2 · Fermat and an odd power of `-1` -/

/-! ### R17. `rintro rfl` · goal `x ≠ 0` with a local `x`: `x` is replaced by `0` everywhere
`x ≠ 0` is `x = 0 → False`; the pattern `rfl` introduces the equation and substitutes it. -/
example {α : Type} [Zero α] (Q : α → Prop) (g : Q 0 → False) (x : α) (hx : Q x) : x ≠ 0 := by
  rintro rfl
  exact g hx

/-! ### R18. `simp at hx` · a hypothesis that simplifies to `False` closes the goal
`(0 : ZMod p) ^ 2 = -1` becomes `0 = -1` (`zero_pow`), then `1 = 0` (`zero_eq_neg`), which `one_ne_zero`
refutes: `1 ≠ 0` in `ZMod p` because `p > 1` (from the instance `[Fact p.Prime]`). -/
example (p : ℕ) [Fact p.Prime] (G : Prop) (hx : (0 : ZMod p) ^ 2 = -1) : G := by
  simp at hx

/-! ### R19. `(Fact.out : p.Prime).two_le` · context gains `2 ≤ p` from the instance `[Fact p.Prime]` -/
example (p : ℕ) [Fact p.Prime] (G : Prop) (g : 2 ≤ p → G) : G := by
  have h2 := (Fact.out : p.Prime).two_le
  exact g h2

/-! ### R20. `haveI : Fact (2 < n) := ⟨h⟩` · context gains an instance that lemmas find by themselves -/
example (n : ℕ) (h : 2 < n) (G : Prop) (g : [Fact (2 < n)] → G) : G := by
  haveI : Fact (2 < n) := ⟨h⟩
  exact g

/-! ### R21. `ZMod.pow_card_sub_one_eq_one` (Fermat) · context gains `a ^ (p - 1) = 1` -/
example (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) (G : Prop) (g : a ^ (p - 1) = 1 → G) :
    G := by
  have hf := ZMod.pow_card_sub_one_eq_one ha
  exact g hf

/-! ### R22. `obtain ⟨k, hk⟩ : ∃ k, … := ⟨w, by omega⟩` · context gains `k` and an equation for it -/
example (n : ℕ) (h : n % 3 = 1) (G : Prop) (g : ∀ k, n = 3 * k + 1 → G) : G := by
  obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
  exact g k hk

/-! ### R23. `pow_mul` with `at h` · context: `a ^ (m * n)` → `(a ^ m) ^ n` inside `h` -/
example {M : Type} [Monoid M] (a : M) (m n : ℕ) (Q : M → Prop) (h : Q (a ^ (m * n)))
    (G : Prop) (g : Q ((a ^ m) ^ n) → G) : G := by
  rw [pow_mul] at h
  exact g h

/-! ### R24. `(odd_two_mul_add_one k).neg_one_pow` · goal: `(-1) ^ (2 * k + 1)` → `-1`
`odd_two_mul_add_one k : Odd (2 * k + 1)`; `Odd.neg_one_pow : Odd n → (-1) ^ n = -1`. -/
example {R : Type} [Ring R] (k : ℕ) (P : R → Prop) (h : P (-1)) : P ((-1) ^ (2 * k + 1)) := by
  rw [(odd_two_mul_add_one k).neg_one_pow]
  exact h

/-! ### R25. `ZMod.neg_one_ne_one` · closes `False` from `h : (-1 : ZMod n) = 1`, given `[Fact (2 < n)]` -/
example (n : ℕ) [Fact (2 < n)] (h : (-1 : ZMod n) = 1) : False := by
  exact ZMod.neg_one_ne_one h

/-! ## Part 3 · the iff: case split on `p`, Wilson -/

/-! ### R26. `rintro ⟨x, hx⟩ hab` · goal `(∃ x, Q x) → a ≠ b` → context `x, hx, hab : a = b`, goal `False` -/
example {α : Type} (Q : α → Prop) (a b : ℕ) (g : ∀ x, Q x → a = b → False) :
    (∃ x, Q x) → a ≠ b := by
  rintro ⟨x, hx⟩ hab
  exact g x hx hab

/-! ### R27. `rcases hp.eq_two_or_odd' with rfl | ⟨m, hm⟩` · goal list: `p = 2` (substituted) | `p` odd
`Nat.Prime.eq_two_or_odd' : p.Prime → p = 2 ∨ Odd p`, and `Odd p` is `∃ m, p = 2 * m + 1`. -/
example (p : ℕ) (hp : p.Prime) (P : ℕ → Prop) (h2 : P 2) (hodd : ∀ m, p = 2 * m + 1 → P p) :
    P p := by
  rcases hp.eq_two_or_odd' with rfl | ⟨m, hm⟩
  · exact h2
  · exact hodd m hm

/-! ### R28. `decide +revert` · closes a concrete `ZMod` goal when a local instance is in context
Plain `decide` refuses: the goal mentions the local `inst✝ : Fact (Nat.Prime 3)`. -/
example [Fact (Nat.Prime 3)] : ∃ x : ZMod 3, x ^ 2 = 1 := by
  refine ⟨2, ?_⟩
  decide +revert

/-! ### R29. `obtain ⟨k, rfl⟩ : ∃ k, n = … := ⟨w, by omega⟩` · `n` is replaced by `3 * k + 1` everywhere -/
example (n : ℕ) (h : n % 3 = 1) (P : ℕ → Prop) (g : ∀ k, P (3 * k + 1)) : P n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
  exact g k

/-! ### R30. `ZMod.wilsons_lemma (p := q)` (Wilson) · context gains `↑(q - 1)! = -1` in `ZMod q` -/
example (q : ℕ) [Fact q.Prime] (G : Prop) (g : ((q - 1).factorial : ZMod q) = -1 → G) : G := by
  have hw := ZMod.wilsons_lemma (p := q)
  exact g hw

/-! ### R31. `Nat.add_sub_cancel` · `n + m - m = n` -/
example (n m : ℕ) (P : ℕ → Prop) (h : P n) : P (n + m - m) := by
  rw [Nat.add_sub_cancel]
  exact h

/-! ### R32. `neg_one_sq` · goal: `(-1) ^ 2` → `1` -/
example {R : Type} [Ring R] (P : R → Prop) (h : P 1) : P ((-1) ^ 2) := by
  rw [neg_one_sq]
  exact h

/-! ### R33. `one_pow` · goal: `1 ^ n` → `1` -/
example {M : Type} [Monoid M] (n : ℕ) (P : M → Prop) (h : P 1) : P (1 ^ n) := by
  rw [one_pow]
  exact h

/-! ### R34. `one_mul` · goal: `1 * a` → `a` -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Two naturals that add up to the modulus are negatives in `ZMod`: R5 → R6 → R7 → R8 -/
example (m : ℕ) (hm : m ≤ 7) : ((7 - m : ℕ) : ZMod 7) = -((m : ℕ) : ZMod 7) := by
  rw [eq_neg_iff_add_eq_zero]
  rw [← Nat.cast_add]
  rw [ZMod.natCast_eq_zero_iff]
  rw [show 7 - m + m = 7 by omega]

/-! ### W2. An odd power of a square root of `-1`: R23 → `rw [hx]` → R24 -/
example (x : ZMod 7) (hx : x ^ 2 = -1) : x ^ (2 * (2 * 1 + 1)) = -1 := by
  rw [pow_mul]
  rw [hx]
  rw [(odd_two_mul_add_one 1).neg_one_pow]

/-! ### W3. Wilson in `ZMod 5`, written as `2 * 2 + 1`: R20 → R30 → R31 -/
example : ((2 * 2).factorial : ZMod (2 * 2 + 1)) = -1 := by
  haveI : Fact (Nat.Prime (2 * 2 + 1)) := ⟨by norm_num⟩
  have hw := ZMod.wilsons_lemma (p := 2 * 2 + 1)
  rw [Nat.add_sub_cancel] at hw
  exact hw

end H034Guide
