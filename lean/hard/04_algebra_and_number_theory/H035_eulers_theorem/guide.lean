/- Guide for H035 (Euler's theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the shift `k ↦ (k + 1) % n` on
`range n`, products of `2 * k`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H035Guide

open Finset

/-! # Part R · Reference entries -/

/-! ## Membership in `range` and `filter` (MILESTONE 1) -/

/-! ### R1. `Finset.mem_filter` · `a ∈ s.filter p ↔ a ∈ s ∧ p a` · `rw [Finset.mem_filter] at h ⊢`
changes a hypothesis and the goal at once. Term form: `Finset.mem_filter.mp h : a ∈ s ∧ p a`. -/
example {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (a b : α)
    (h : a ∈ s.filter p) (k : a ∈ s ∧ p a → b ∈ s ∧ p b) : b ∈ s.filter p := by
  rw [Finset.mem_filter] at h ⊢
  exact k h

/-! ### R2. `Finset.mem_range` · `m ∈ range n ↔ m < n` · goal (or hypothesis) -/
example (m n : ℕ) (P : Prop → Prop) (h : P (m < n)) : P (m ∈ range n) := by
  rw [Finset.mem_range]
  exact h

/-! ### R3. `Nat.mod_lt` · `0 < n → m % n < n` · in `refine ⟨Nat.mod_lt _ hn, ?_⟩`: goal list loses
the first half of an `∧` -/
example (m n : ℕ) (hn : 0 < n) (Q : Prop) (hq : Q) : m % n < n ∧ Q := by
  refine ⟨Nat.mod_lt _ hn, ?_⟩
  exact hq

/-! ### R4. `Nat.Coprime` (unfold) · goal `m.Coprime n` → `m.gcd n = 1` -/
example (m n : ℕ) (h : m.gcd n = 1) : m.Coprime n := by
  rw [Nat.Coprime]
  exact h

/-! ### R5. `Nat.gcd_comm` · `gcd m n = gcd n m` · goal -/
example (m n : ℕ) (P : ℕ → Prop) (h : P (n.gcd m)) : P (m.gcd n) := by
  rw [Nat.gcd_comm]
  exact h

/-! ### R6. `Nat.gcd_rec` · `gcd m n = gcd (n % m) m`; right to left: `gcd (n % m) m` → `gcd m n` -/
example (m n : ℕ) (P : ℕ → Prop) (h : P (m.gcd n)) : P ((n % m).gcd m) := by
  rw [← Nat.gcd_rec]
  exact h

/-! ### R7. `Nat.Coprime.symm` · `m.Coprime n → n.Coprime m` (dot notation `h.symm`) · context -/
example (m n : ℕ) (h : m.Coprime n) (G : Prop) (k : n.Coprime m → G) : G := by
  have h' := h.symm
  exact k h'

/-! ### R8. `Nat.Coprime.mul_right` · `k.Coprime m → k.Coprime n → k.Coprime (m * n)` · goal closed
The goal may be the unfolded form `k.gcd (m * n) = 1`: it is the same proposition (R4). -/
example (k m n : ℕ) (hm : k.Coprime m) (hn : k.Coprime n) : k.gcd (m * n) = 1 := by
  exact Nat.Coprime.mul_right hm hn

/-! ## Injectivity on a finset and `≡ [MOD n]` (MILESTONE 2) -/

/-! ### R9. `Set.InjOn f ↑s` · `intro x hx y hy hxy` · goal: injectivity on `s` → `x = y`
`↑s` is the finset `s` seen as a set. -/
example {α β : Type} (f : α → β) (s : Finset α) (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    Set.InjOn f ↑s := by
  intro x hx y hy hxy
  exact h x hx y hy hxy

/-! ### R10. `Finset.coe_filter` · `↑(s.filter p) = {x | x ∈ s ∧ p x}` · goal (or `at hx`) -/
example {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (x : α) (P : Prop → Prop)
    (h : P (x ∈ {x | x ∈ s ∧ p x})) : P (x ∈ (↑(s.filter p) : Set α)) := by
  rw [Finset.coe_filter]
  exact h

/-! ### R11. `Set.mem_setOf_eq` · `(a ∈ {x | q x}) = q a` · goal (or `at hx`) -/
example {α : Type} (q : α → Prop) (a : α) (P : Prop → Prop) (h : P (q a)) : P (a ∈ {x | q x}) := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R12. `have h' : a ≡ b [MOD n] := h` · a `%`-equation IS a congruence
(`Nat.ModEq n a b` is defined as `a % n = b % n`), so `h` proves it as it stands · context.
Inside a term the same relabelling is the ascription `(h : a ≡ b [MOD n])`. -/
example (a b n : ℕ) (h : a % n = b % n) (G : Prop) (k : a ≡ b [MOD n] → G) : G := by
  have h' : a ≡ b [MOD n] := h
  exact k h'

/-! ### R13. `Nat.ModEq.cancel_left_of_coprime` · `m.gcd c = 1 → c * a ≡ c * b [MOD m] → a ≡ b [MOD m]`
· context gains the cancelled congruence. `hmc` may be `hc : m.Coprime c` (same proposition, R4). -/
example (m c a b : ℕ) (hc : m.Coprime c) (h : c * a ≡ c * b [MOD m]) (G : Prop)
    (k : a ≡ b [MOD m] → G) : G := by
  have h' := Nat.ModEq.cancel_left_of_coprime hc h
  exact k h'

/-! ### R14. `unfold Nat.ModEq at h` · hypothesis: `a ≡ b [MOD n]` → `a % n = b % n` -/
example (a b n : ℕ) (h : a ≡ b [MOD n]) (G : Prop) (k : a % n = b % n → G) : G := by
  unfold Nat.ModEq at h
  exact k h

/-! ### R15. `Nat.mod_eq_of_lt` · `a < b → a % b = a` · hypothesis (or goal) -/
example (a b : ℕ) (hab : a < b) (P : ℕ → Prop) (h : P (a % b)) (k : P a → False) : False := by
  rw [Nat.mod_eq_of_lt hab] at h
  exact k h

/-! ### R16. `rwa [e] at h` · `rw [e] at h`, then `assumption` · goal closed -/
example (a b x : ℕ) (e : a = b) (h : x = a) : x = b := by
  rwa [e] at h

/-! ## Equal by inclusion and size (MILESTONE 3) -/

/-! ### R17. `Finset.eq_of_subset_of_card_le` · `s ⊆ t → #t ≤ #s → s = t` · `apply`: goal → two goals
`#s` is `Finset.card s`, the number of elements of `s`. -/
example {α : Type} (s t : Finset α) (h1 : s ⊆ t) (h2 : #t ≤ #s) : s = t := by
  apply Finset.eq_of_subset_of_card_le
  · exact h1
  · exact h2

/-! ### R18. `intro x hx` on `s ⊆ t` · goal `s ⊆ t` → `x ∈ t`, context gains `hx : x ∈ s` -/
example {α : Type} (s t : Finset α) (h : ∀ x, x ∈ s → x ∈ t) : s ⊆ t := by
  intro x hx
  exact h x hx

/-! ### R19. `Finset.mem_image` · `b ∈ s.image f ↔ ∃ a ∈ s, f a = b` · goal (or `at hb`) -/
example {α β : Type} [DecidableEq β] (s : Finset α) (f : α → β) (b : β) (P : Prop → Prop)
    (h : P (∃ a ∈ s, f a = b)) : P (b ∈ s.image f) := by
  rw [Finset.mem_image]
  exact h

/-! ### R20. `obtain ⟨a, ha, rfl⟩ := h` · context: `h : ∃ a ∈ s, f a = b` → `a`, `ha`, and `b` replaced
by `f a` everywhere -/
example {α β : Type} (s : Finset α) (f : α → β) (b : β) (h : ∃ a ∈ s, f a = b)
    (P : β → Prop) (k : ∀ a ∈ s, P (f a)) : P b := by
  obtain ⟨a, ha, rfl⟩ := h
  exact k a ha

/-! ### R21. `Finset.card_image_of_injOn` · `Set.InjOn f ↑s → #(s.image f) = #s` · goal
`rw` then tries `rfl`, so a goal that becomes `#s ≤ #s` is closed on the spot. -/
example {α β : Type} [DecidableEq β] (s : Finset α) (f : α → β) (hf : Set.InjOn f ↑s)
    (P : ℕ → Prop) (h : P #s) : P #(s.image f) := by
  rw [Finset.card_image_of_injOn hf]
  exact h

/-! ## The product argument (`euler`) -/

/-! ### R22. `rcases Nat.eq_zero_or_pos n with rfl | hn` · `n = 0 ∨ 0 < n` · goal list: the `n = 0`
case with `n` replaced by `0`, and the case with `hn : 0 < n` -/
example (P : ℕ → Prop) (n : ℕ) (h0 : P 0) (hpos : ∀ m, 0 < m → P m) : P n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact h0
  · exact hpos n hn

/-! ### R23. `Nat.totient_zero`, `pow_zero` · `φ 0 = 0`, `a ^ 0 = 1` · goal (`simp` uses both itself) -/
example (a : ℕ) (P : ℕ → Prop) (h : P 1) : P (a ^ Nat.totient 0) := by
  simp only [Nat.totient_zero, pow_zero]
  exact h

/-! ### R24. `Nat.ModEq.refl` · `a ≡ a [MOD n]` · goal closed (`simp` knows it) -/
example (a n : ℕ) : a ≡ a [MOD n] := by
  exact Nat.ModEq.refl a

/-! ### R25. `set x := e with hx` · every `e` (goal and context) becomes `x`; context gains
`x : α := e` and `hx : x = e` -/
example (n : ℕ) (P : Finset ℕ → Prop) (h : P (range (n + 1))) : P (range (n + 1)) := by
  set s := range (n + 1) with hs
  exact h

/-! ### R26. `conv_lhs => rw [← h]` · rewrites only the left-hand side of an equation goal -/
example {α β : Type} (f : α → β) (x y : α) (h : y = x) (k : f y = f x) : f x = f x := by
  conv_lhs => rw [← h]
  exact k

/-! ### R27. `Finset.prod_image` · `Set.InjOn g ↑s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x)` · goal
`∏ x ∈ s, f x` is `Finset.prod s f`: the product of `f x` over the elements of `s`. -/
example {α β : Type} [DecidableEq α] (s : Finset β) (g : β → α) (f : α → ℕ)
    (hg : Set.InjOn g ↑s) (P : ℕ → Prop) (h : P (∏ x ∈ s, f (g x))) :
    P (∏ x ∈ s.image g, f x) := by
  rw [Finset.prod_image hg]
  exact h

/-! ### R28. `Nat.coprime_prod_right_iff` · `x.Coprime (∏ i ∈ t, s i) ↔ ∀ i ∈ t, x.Coprime (s i)`
· `apply ….mpr`: goal → one coprimality per factor -/
example {ι : Type} (x : ℕ) (t : Finset ι) (s : ι → ℕ) (h : ∀ i ∈ t, x.Coprime (s i)) :
    x.Coprime (∏ i ∈ t, s i) := by
  apply Nat.coprime_prod_right_iff.mpr
  exact h

/-! ### R29. `Finset.prod_mul_distrib` · `∏ i ∈ s, f i * g i = (∏ i ∈ s, f i) * ∏ i ∈ s, g i` · goal -/
example {ι : Type} (s : Finset ι) (f g : ι → ℕ) (P : ℕ → Prop)
    (h : P ((∏ i ∈ s, f i) * ∏ i ∈ s, g i)) : P (∏ i ∈ s, f i * g i) := by
  rw [Finset.prod_mul_distrib]
  exact h

/-! ### R30. `Finset.prod_const` · `∏ _x ∈ s, b = b ^ #s` · goal -/
example {ι : Type} (s : Finset ι) (b : ℕ) (P : ℕ → Prop) (h : P (b ^ #s)) :
    P (∏ _i ∈ s, b) := by
  rw [Finset.prod_const]
  exact h

/-! ### R31. `Nat.totient_eq_card_coprime` · `n.totient = #{a ∈ range n | n.Coprime a}` · goal
`{a ∈ s | p a}` is how Lean prints `s.filter p`. -/
example (n : ℕ) (P : ℕ → Prop) (h : P #{a ∈ range n | n.Coprime a}) : P n.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact h

/-! ### R32. `mul_comm`, `mul_one` · `a * b = b * a`, `a * 1 = a` · goal
A bare `rw [mul_comm]` rewrites the first product it finds; `mul_comm a b` picks one. -/
example (a b : ℕ) (P : ℕ → Prop) (h : P (b * a)) : P (a * b * 1) := by
  rw [mul_one]
  rw [mul_comm]
  exact h

/-! ### R33. `Finset.prod_nat_mod` · `(∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n` · goal closed
(as a term: `Finset.prod_nat_mod s n f`) -/
example {ι : Type} (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n := by
  exact Finset.prod_nat_mod s n f

/-! ### R34. `calc` on `% n` for a goal `a ≡ b [MOD n]` · goal closed by a chain `a % n = … = b % n`
(R12: the congruence is the `%`-equation) -/
example (a b c n : ℕ) (h1 : a % n = c % n) (h2 : c % n = b % n) : a ≡ b [MOD n] := by
  calc a % n = c % n := h1
    _ = b % n := h2

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `k ↦ (k + 1) % n` maps `range n` into itself, and `%` is idle below `n`: R2, R3, R15 -/
example (n k : ℕ) (hn : 0 < n) (hk : k ∈ range n) : (k + 1) % n ∈ range n ∧ k % n = k := by
  rw [Finset.mem_range] at hk ⊢
  exact ⟨Nat.mod_lt _ hn, Nat.mod_eq_of_lt hk⟩

/-! ### W2. Drop a `%` inside a coprimality (R4, R5, R6, R7); coprime to a product of three (R8 twice) -/
example (m c : ℕ) (hc : c.Coprime m) : m.Coprime (c % m) := by
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
  exact hc.symm

example (n b c d : ℕ) (hb : n.Coprime b) (hc : n.Coprime c) (hd : n.Coprime d) :
    n.Coprime (b * c * d) := by
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right hb hc) hd

/-! ### W3. An image that is the whole finset, by inclusion and size: R17, R18, R19, R20, R21 -/
example (n : ℕ) (hn : 0 < n) (hinj : Set.InjOn (fun k => (k + 1) % n) ↑(range n)) :
    (range n).image (fun k => (k + 1) % n) = range n := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range]
    exact Nat.mod_lt _ hn
  · rw [Finset.card_image_of_injOn hinj]

/-! ### W4. Reindex a product along that image: R26, R27 -/
example (n : ℕ) (himg : (range n).image (fun k => (k + 1) % n) = range n)
    (hinj : Set.InjOn (fun k => (k + 1) % n) ↑(range n)) :
    ∏ k ∈ range n, (k + 1) = ∏ k ∈ range n, ((k + 1) % n + 1) := by
  conv_lhs => rw [← himg]
  rw [Finset.prod_image hinj]

/-! ### W5. Pull a constant factor out of a product, then reduce mod n: R29, R30, R33, R34 -/
example (s : Finset ℕ) (n : ℕ) :
    (2 ^ #s * ∏ k ∈ s, k) ≡ ∏ k ∈ s, 2 * k % n [MOD n] := by
  have hpow : ∏ k ∈ s, 2 * k = 2 ^ #s * ∏ k ∈ s, k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc (2 ^ #s * ∏ k ∈ s, k) % n = (∏ k ∈ s, 2 * k) % n := by rw [hpow]
    _ = (∏ k ∈ s, 2 * k % n) % n := Finset.prod_nat_mod _ _ _

end H035Guide
