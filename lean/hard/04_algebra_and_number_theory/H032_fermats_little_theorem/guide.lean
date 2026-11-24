/- Guide for H032 (Fermat's little theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is an
arbitrary goal and a hypothesis `h` or `g` in an entry is only there to finish the example; it shows
what the goal (or the new hypothesis) became.
Part W: worked combinations on facts that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H032Guide

/-! # Part R · Reference entries -/

/-! ## Divisibility of a sum, term by term -/

/-! ### R1. `apply Finset.dvd_sum` · goal: `d ∣ ∑ i ∈ s, f i` → `∀ i ∈ s, d ∣ f i`
`s : Finset ι` is a finite set; `∑ i ∈ s, f i` is the sum of `f i` over `i ∈ s`. -/
example {ι : Type} (s : Finset ι) (f : ι → ℕ) (d : ℕ) (h : ∀ i ∈ s, d ∣ f i) :
    d ∣ ∑ i ∈ s, f i := by
  apply Finset.dvd_sum
  exact h

/-! ### R2. `intro i hi` on `∀ i ∈ s, Q i` · context gains `i` and `hi : i ∈ s`
`∀ i ∈ s, Q i` is notation for `∀ i, i ∈ s → Q i`: two binders, so `intro` takes two names. -/
example {ι : Type} (s : Finset ι) (Q : ι → Prop) (h : ∀ i, i ∈ s → Q i) : ∀ i ∈ s, Q i := by
  intro i hi
  exact h i hi

/-! ### R3. `rw [Finset.mem_range] at hi` · `m ∈ range n ↔ m < n` · context: membership → inequality
`Finset.range n` is the finite set `{0, 1, …, n - 1}`. -/
example (n i : ℕ) (G : Prop) (hi : i ∈ Finset.range n) (g : i < n → G) : G := by
  rw [Finset.mem_range] at hi
  exact g hi

/-! ### R4. `Nat.Prime.dvd_choose_self` · `p.Prime → k ≠ 0 → k < p → p ∣ p.choose k` · goal → two side goals
`p.choose k` is the binomial coefficient C(p, k). As a term: `hp.dvd_choose_self hk hkp`. -/
example (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) (hkp : k < p) : p ∣ p.choose k := by
  apply hp.dvd_choose_self
  exact hk
  exact hkp

/-! ### R5. `Nat.succ_ne_zero` · `n.succ ≠ 0`; `n.succ` is `n + 1` by definition · closes the goal -/
example (i : ℕ) : i + 1 ≠ 0 := by
  exact Nat.succ_ne_zero i

/-! ### R6. `omega` · closes linear arithmetic over ℕ and ℤ (`+`, `-`, `<`, `≤`, numerals) from the context -/
example (k n : ℕ) (hk : k < n) : k + 1 < n + 1 := by
  omega

/-! ### R7. `Dvd.dvd.mul_left` · `a ∣ b → ∀ c, a ∣ c * b` · goal: `d ∣ c * b` → `d ∣ b`
As a term: `h.mul_left c` (or `h.mul_left _`) for `h : d ∣ b`. -/
example (d b c : ℕ) (h : d ∣ b) : d ∣ c * b := by
  apply Dvd.dvd.mul_left
  exact h

/-! ## Writing `p` as `q + 1` -/

/-! ### R8. `Nat.Prime.one_lt` · `p.Prime → 1 < p` · context gains `1 < p`
`have := hp.one_lt` names it `this`. -/
example (p : ℕ) (hp : p.Prime) (G : Prop) (g : 1 < p → G) : G := by
  have h := hp.one_lt
  exact g h

/-! ### R9. `obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩` · context: `p` is replaced by `q + 1` everywhere
The pattern `rfl` substitutes the equation `p = q + 1` instead of naming it. -/
example (p : ℕ) (hp1 : 1 < p) (Q : ℕ → Prop) (h : ∀ q, Q (q + 1)) : Q p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact h q

/-! ## The binomial theorem and its two end terms -/

/-! ### R10. `add_pow` · `(x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m)` · goal
`↑(n.choose m)` is the natural number C(n, m) cast into `R`. -/
example {R : Type} [CommSemiring R] (x y : R) (n : ℕ) (P : R → Prop)
    (h : P (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * (n.choose m : R))) :
    P ((x + y) ^ n) := by
  rw [add_pow]
  exact h

/-! ### R11. `Finset.sum_range_succ` · goal: split off the LAST term `f n` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ i ∈ Finset.range n, f i + f n)) : P (∑ i ∈ Finset.range (n + 1), f i) := by
  rw [Finset.sum_range_succ]
  exact h

/-! ### R12. `Finset.sum_range_succ'` · goal: split off the FIRST term `f 0`; the rest is reindexed by `i + 1` -/
example {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) (P : M → Prop)
    (h : P (∑ i ∈ Finset.range n, f (i + 1) + f 0)) : P (∑ i ∈ Finset.range (n + 1), f i) := by
  rw [Finset.sum_range_succ']
  exact h

/-! ### R13. `one_pow` · `1 ^ n = 1` · goal -/
example {M : Type} [Monoid M] (n : ℕ) (P : M → Prop) (h : P 1) : P (1 ^ n) := by
  rw [one_pow]
  exact h

/-! ### R14. `mul_one` · `a * 1 = a` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P a) : P (a * 1) := by
  rw [mul_one]
  exact h

/-! ### R15. `Nat.choose_self` · `n.choose n = 1` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P 1) : P (n.choose n) := by
  rw [Nat.choose_self]
  exact h

/-! ### R16. `Nat.sub_self` · `n - n = 0` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P 0) : P (n - n) := by
  rw [Nat.sub_self]
  exact h

/-! ### R17. `pow_zero` · `a ^ 0 = 1` · goal -/
example {M : Type} [Monoid M] (a : M) (P : M → Prop) (h : P 1) : P (a ^ 0) := by
  rw [pow_zero]
  exact h

/-! ### R18. `Nat.choose_zero_right` · `n.choose 0 = 1` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P 1) : P (n.choose 0) := by
  rw [Nat.choose_zero_right]
  exact h

/-! ### R19. `Nat.cast_id` · `(↑n : ℕ) = n` · goal: drops the (trivial) cast ℕ → ℕ that `add_pow` leaves -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Nat.cast n) := by
  rw [Nat.cast_id]
  exact h

/-! ## Congruences `a ≡ b [MOD n]` -/

/-! ### R20. `Nat.modEq_zero_iff_dvd` · `a ≡ 0 [MOD n] ↔ n ∣ a` · context gains `a ≡ 0 [MOD n]` (with `.mpr`) -/
example (n a : ℕ) (G : Prop) (h : n ∣ a) (g : a ≡ 0 [MOD n] → G) : G := by
  have h' := Nat.modEq_zero_iff_dvd.mpr h
  exact g h'

/-! ### R21. `Nat.ModEq.add_right` · `a ≡ b [MOD n] → a + c ≡ b + c [MOD n]` · context (as `h.add_right c`) -/
example (n a b c : ℕ) (G : Prop) (h : a ≡ b [MOD n]) (g : a + c ≡ b + c [MOD n] → G) : G := by
  have h' := h.add_right c
  exact g h'

/-! ### R22. `calc` mixing `≡ [MOD n]` and `=` · closes `a ≡ c [MOD n]` from a chain of steps
The first left side may be `_` (Lean takes it from the goal). The chain is a `≡` as soon as one step is. -/
example (n a b c : ℕ) (h : a ≡ b [MOD n]) (e : b = c) : a ≡ c [MOD n] := by
  calc _ ≡ b [MOD n] := h
    _ = c := e

/-! ### R23. `ring` · closes an identity of commutative (semi)rings; `s`, `t` are unknowns -/
example (s t : ℕ) : 0 + s + t = t + s := by
  ring

/-! ## Induction and the zero case -/

/-! ### R24. `induction a` · goal `Q a` → `Q 0` and `Q (a + 1)` with the IH
Lean's own names carry `✝`; `induction a with | zero => … | succ a ih => …` (or `case succ a ih =>`)
names them `a`, `ih`. -/
example (Q : ℕ → Prop) (h0 : Q 0) (hs : ∀ a, Q a → Q (a + 1)) (a : ℕ) : Q a := by
  induction a
  case zero => exact h0
  case succ a ih => exact hs a ih

/-! ### R25. `Nat.Prime.pos` · `p.Prime → 0 < p` · context gains `0 < p` -/
example (p : ℕ) (hp : p.Prime) (G : Prop) (g : 0 < p → G) : G := by
  have h := hp.pos
  exact g h

/-! ### R26. `Nat.zero_pow` · `0 < n → 0 ^ n = 0` · goal
After a `rw`, Lean tries `rfl`; it closes `0 ≡ 0 [MOD m]` by itself (W5). -/
example (n : ℕ) (hn : 0 < n) (P : ℕ → Prop) (h : P 0) : P (0 ^ n) := by
  rw [Nat.zero_pow hn]
  exact h

/-! ### R27. `Nat.ModEq.trans` · `a ≡ b → b ≡ c → a ≡ c` (all `[MOD n]`) · goal: `a ≡ c` → `b ≡ c` -/
example (n a b c : ℕ) (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  refine h1.trans ?_
  exact h2

/-! ## Cancelling a factor coprime to the modulus -/

/-! ### R28. `Nat.Prime.coprime_iff_not_dvd` · `p.Prime → (p.Coprime n ↔ ¬p ∣ n)` · context (with `.mpr`)
`p.Coprime n` is by definition `p.gcd n = 1`. -/
example (p n : ℕ) (hp : p.Prime) (hn : ¬ p ∣ n) (G : Prop) (g : p.Coprime n → G) : G := by
  have hc := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn
  exact g hc

/-! ### R29. `apply Nat.ModEq.cancel_left_of_coprime hc` · `m.gcd c = 1 → c * a ≡ c * b → a ≡ b` · goal
A `hc : m.Coprime c` is accepted for `m.gcd c = 1` (same thing by definition). -/
example (m a b c : ℕ) (hc : m.Coprime c) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  apply Nat.ModEq.cancel_left_of_coprime hc
  exact h

/-! ### R30. `pow_succ'` · `a ^ (n + 1) = a * a ^ n`; right to left: `rw [← pow_succ']` · goal -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ (n + 1))) :
    P (a * a ^ n) := by
  rw [← pow_succ']
  exact h

/-! ### R31. `LT.lt.le` · `a < b → a ≤ b` · context (as `h.le`) -/
example (a b : ℕ) (G : Prop) (h : a < b) (g : a ≤ b → G) : G := by
  have h' := h.le
  exact g h'

/-! ### R32. `Nat.sub_add_cancel` · `m ≤ n → n - m + m = n` · goal
ℕ subtraction is truncated (`1 - 2 = 0`), so the cancellation needs `m ≤ n`. -/
example (n m : ℕ) (hm : m ≤ n) (P : ℕ → Prop) (h : P n) : P (n - m + m) := by
  rw [Nat.sub_add_cancel hm]
  exact h

/-! # Part W · Worked combinations (not the exercise's facts) -/

/-! ### W1. Peel both ends of a sum over `range (n + 1 + 1)`: R11, then R12 -/
example (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1 + 1), f i = ∑ i ∈ Finset.range n, f (i + 1) + f 0 + f (n + 1) := by
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ']

/-! ### W2. Clean one binomial term with `y = 1` in ℕ: R13, R14, R19 in one `simp only` -/
example (x k m : ℕ) :
    x ^ m * 1 ^ (k - m) * (Nat.cast (k.choose m) : ℕ) = x ^ m * k.choose m := by
  simp only [one_pow, mul_one, Nat.cast_id]

/-! ### W3. Divisible part ≡ 0, then shift: R20, R21, R22, R23 -/
example (n s t : ℕ) (h : n ∣ s) : s + t ≡ t [MOD n] := by
  have h0 := Nat.modEq_zero_iff_dvd.mpr h
  calc _ ≡ 0 + t [MOD n] := h0.add_right t
    _ = t := by ring

/-! ### W4. Chain two congruences: R21, R27 -/
example (n a b c : ℕ) (h1 : a ≡ b [MOD n]) (h2 : b + 2 ≡ c [MOD n]) : a + 2 ≡ c [MOD n] := by
  exact (h1.add_right 2).trans h2

/-! ### W5. The zero case closes after one `rw` (R26 and the automatic `rfl`) -/
example (m n : ℕ) (hn : 0 < n) : 0 ^ n ≡ 0 [MOD m] := by
  rw [Nat.zero_pow hn]

/-! ### W6. Cancel `3` modulo `7` (gcd 7 3 = 1 by `norm_num`): R29 -/
example (a b : ℕ) (h : 3 * a ≡ 3 * b [MOD 7]) : a ≡ b [MOD 7] := by
  apply Nat.ModEq.cancel_left_of_coprime (by norm_num : Nat.gcd 7 3 = 1)
  exact h

/-! ### W7. Truncated exponent `n - 1` put back together: R30, R31, R32 -/
example (a n : ℕ) (hn : 1 < n) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ']
  rw [Nat.sub_add_cancel hn.le]

end H032Guide
