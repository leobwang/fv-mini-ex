/- Guide for M058 (Casting out nines).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `g : … → G`) in an entry is only there to finish the example; it shows what the
goal or the context became.
Part W: worked combinations on objects that are NOT the exercise's (base 100, mod 11, base 7).
Assumed: Lean basics.
-/
import Mathlib

namespace M058Guide

/-! # Part R · Reference entries -/

/-! ## Congruences `a ≡ b [MOD n]` -/

/-! ### R1. `unfold Nat.ModEq` · goal: `a ≡ b [MOD n]` → `a % n = b % n`
`a ≡ b [MOD n]` is notation for `Nat.ModEq n a b`, which is *defined* as `a % n = b % n`. -/
example (n a b : ℕ) (h : a % n = b % n) : a ≡ b [MOD n] := by
  unfold Nat.ModEq
  exact h

/-! ### R2. `decide` · closes a congruence between numerals (Lean computes both remainders) -/
example : 100 ≡ 1 [MOD 11] := by decide

/-! ### R3. `Nat.ModEq.pow` · `a ≡ b [MOD n] → a ^ k ≡ b ^ k [MOD n]` · context gains the power
Dot notation: for `h : a ≡ b [MOD n]`, `h.pow k` is `Nat.ModEq.pow k h`. -/
example (n a b k : ℕ) (h : a ≡ b [MOD n]) (G : Prop) (g : a ^ k ≡ b ^ k [MOD n] → G) : G := by
  have h' := h.pow k
  exact g h'

/-! ### R4. `simpa using e` · closes the goal with `e` after `simp` tidies both (`one_pow : 1 ^ k = 1`) -/
example (n a k : ℕ) (h : a ≡ 1 ^ k [MOD n]) : a ≡ 1 [MOD n] := by
  simpa using h

/-! ## Strong induction and the case `n = 0` -/

/-! ### R5. `induction n using Nat.strong_induction_on with | _ n ih => …` · context gains
`ih : ∀ m < n, P m`: the claim for every smaller number. Written the way the exercise uses it
(`_` matches the one case, which Lean calls `h`; `n ih` name the number and the hypothesis): -/
example (P : ℕ → Prop) (step : ∀ n, (∀ m < n, P m) → P n) (n : ℕ) : P n := by
  induction n using Nat.strong_induction_on with
    | _ n ih => exact step n ih

/-! The same step without `with`, so the infoview shows the state between two tactics. Without
`with`, the new names are inaccessible (`n✝`, `a✝`); `rename_i n ih` names them. -/
example (P : ℕ → Prop) (step : ∀ n, (∀ m < n, P m) → P n) (n : ℕ) : P n := by
  induction n using Nat.strong_induction_on
  rename_i n ih
  exact step n ih

/-! ### R6. `rcases Nat.eq_zero_or_pos n with rfl | hn` · goal list: case `n = 0` and case `0 < n`
`Nat.eq_zero_or_pos n : n = 0 ∨ n > 0`. The pattern `rfl` substitutes `0` for `n` in the first goal. -/
example (P : ℕ → Prop) (h0 : P 0) (hpos : ∀ n, 0 < n → P n) (n : ℕ) : P n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  exact h0
  exact hpos n hn

/-! ### R7. `rfl` · closes `a ≡ b [MOD n]` when both sides compute to the same remainder
It works because `Nat.ModEq` is an `=` underneath (R1). `Nat.digits b 0` computes to `[]`. -/
example (n a : ℕ) : a ≡ a [MOD n] := by rfl

/-! The right side may need computing first: `Nat.digits 7 0` is `[]`, and `[].sum` is `0`. -/
example (n : ℕ) : 0 ≡ (Nat.digits 7 0).sum [MOD n] := by rfl

/-! ## Digits of a number -/

/-! ### R8. `Nat.digits_def'` · `1 < b → 0 < n → b.digits n = n % b :: b.digits (n / b)` · goal
`Nat.digits b n` (printed `b.digits n`) lists the base-`b` digits of `n`, least significant first.
Write `rw [Nat.digits_def' (by norm_num) hn]` when `b` is a numeral. -/
example (b n : ℕ) (hb : 1 < b) (hn : 0 < n) (P : List ℕ → Prop)
    (h : P (n % b :: b.digits (n / b))) : P (b.digits n) := by
  rw [Nat.digits_def' hb hn]
  exact h

/-! ### R9. `List.sum_cons` · `(a :: l).sum = a + l.sum` · goal: the sum of a cons → head + sum of tail -/
example (a : ℕ) (l : List ℕ) (P : ℕ → Prop) (h : P (a + l.sum)) : P (a :: l).sum := by
  rw [List.sum_cons]
  exact h

/-! ### R10. `Nat.div_lt_self` · `0 < n → 1 < k → n / k < n` · context gains the bound for `ih` -/
example (n k : ℕ) (hn : 0 < n) (hk : 1 < k) (G : Prop) (g : n / k < n → G) : G := by
  have hlt : n / k < n := Nat.div_lt_self hn hk
  exact g hlt

/-! ## Chaining congruences -/

/-! ### R11. `calc` · goal list: a chain of `=` and `≡ [MOD n]` steps, one goal per `?_`
Each step starts with `_` (the previous right side). `=` and `≡ [MOD n]` mix freely. -/
example (n a b c : ℕ) (h1 : a = b) (h2 : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  calc a = b := ?_
    _ ≡ c [MOD n] := ?_
  exact h1
  exact h2

/-! ### R12. `Nat.mod_add_div` · `m % k + k * (m / k) = m` · context gains it; `.symm` flips it -/
example (m k : ℕ) (G : Prop) (g : m = m % k + k * (m / k) → G) : G := by
  have h := (Nat.mod_add_div m k).symm
  exact g h

/-! ### R13. `Nat.ModEq.mul_right` · `a ≡ b [MOD n] → a * c ≡ b * c [MOD n]` · context -/
example (n a b c : ℕ) (h : a ≡ b [MOD n]) (G : Prop) (g : a * c ≡ b * c [MOD n] → G) : G := by
  have h' := h.mul_right c
  exact g h'

/-! ### R14. `Nat.ModEq.add_left` · `a ≡ b [MOD n] → c + a ≡ c + b [MOD n]` · closes the goal
`exact h.add_left _`: Lean reads `c` off the goal, so `_` is enough. -/
example (n a b c : ℕ) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] := by
  exact h.add_left _

/-! ### R15. `one_mul` · `1 * a = a` · goal -/
example {M : Type} [MulOneClass M] (a : M) (P : M → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ## From congruence to divisibility -/

/-! ### R16. `Nat.modEq_zero_iff_dvd` · `a ≡ 0 [MOD n] ↔ n ∣ a` · goal; right to left: `rw [← …]` -/
example (n a : ℕ) (P : Prop → Prop) (h : P (a ≡ 0 [MOD n])) : P (n ∣ a) := by
  rw [← Nat.modEq_zero_iff_dvd]
  exact h

/-! ### R17. `refine ⟨fun h => ?_, fun h => ?_⟩` · goal list: `A ↔ B` → two goals, each with `h` -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  exact f h
  exact g h

/-! ### R18. `Nat.ModEq.symm` · `a ≡ b [MOD n] → b ≡ a [MOD n]` · context -/
example (n a b : ℕ) (h : a ≡ b [MOD n]) (G : Prop) (g : b ≡ a [MOD n] → G) : G := by
  have h' := h.symm
  exact g h'

/-! ### R19. `Nat.ModEq.trans` · `a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n]` · closes the goal -/
example (n a b c : ℕ) (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  exact h1.trans h2

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A power congruence: R2, R3, R4 -/
example (k : ℕ) : 100 ^ k ≡ 1 [MOD 11] := by
  have h : 100 ≡ 1 [MOD 11] := by decide
  simpa using h.pow k

/-! ### W2. Peel off the last base-100 "digit" and drop the `100` mod 99: R11, R12, R13, R14, R15 -/
example (n : ℕ) : n ≡ n % 100 + n / 100 [MOD 99] := by
  have h100 : 100 ≡ 1 [MOD 99] := by decide
  calc n = n % 100 + 100 * (n / 100) := (Nat.mod_add_div n 100).symm
    _ ≡ n % 100 + 1 * (n / 100) [MOD 99] := (h100.mul_right _).add_left _
    _ = n % 100 + n / 100 := by rw [one_mul]

/-! ### W3. Digits in base 7: R8 with a numeral base, then R9 -/
example (n : ℕ) (hn : 0 < n) (P : ℕ → Prop) (h : P (n % 7 + (Nat.digits 7 (n / 7)).sum)) :
    P (Nat.digits 7 n).sum := by
  rw [Nat.digits_def' (by norm_num) hn]
  rw [List.sum_cons]
  exact h

/-! ### W4. Divisibility from a congruence: R16 in a hypothesis and the goal at once, then R19 -/
example (a b : ℕ) (hab : a ≡ b [MOD 11]) (hb : 11 ∣ b) : 11 ∣ a := by
  rw [← Nat.modEq_zero_iff_dvd] at hb ⊢
  exact hab.trans hb

end M058Guide
