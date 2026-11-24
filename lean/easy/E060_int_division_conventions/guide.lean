/- Guide for E060 (Int division conventions).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
R1–R3, R7, R8 and R14 use other numbers than the exercise: `decide` needs concrete values.
Part W: worked combinations on objects that are NOT the exercise's (other moduli, other functions).
Assumed: Lean basics (E001–E033).
-/

namespace E060Guide

/-! # Part R · Reference entries -/

/-! ## What `/`, `%`, `tdiv` compute (closed by `decide`) -/

/-! ### R1. `/` on `Int` is `Int.ediv` · `decide` closes a literal fact
`a / b` with `b > 0` rounds DOWN (toward −∞): `-9 / 4 = -3`, since `-9 = 4 * (-3) + 3`. -/
example : (-9 : Int) / 4 = -3 := by
  decide

/-! ### R2. `%` on `Int` is `Int.emod` · `decide` closes a literal fact
The remainder is never negative: `0 ≤ a % b < |b|` for `b ≠ 0`, and `a = b * (a / b) + a % b`. -/
example : (-9 : Int) % 4 = 3 := by
  decide

/-! ### R3. `Int.tdiv`, `Int.tmod` · truncation toward 0 (C, Rust, Java `/`, `%`)
The remainder takes the sign of `a`: `-9 = 4 * (-2) + (-1)`. -/
example : (-9 : Int).tdiv 4 = -2 ∧ (-9 : Int).tmod 4 = -1 := by
  decide

/-! ## Division by zero -/

/-! ### R4. `Int.ediv_zero` · `a / 0 = 0` · goal -/
example (a : Int) (P : Int → Prop) (h : P 0) : P (a / 0) := by
  rw [Int.ediv_zero]
  exact h

/-! ### R5. `Int.emod_zero` · `a % 0 = a` · goal -/
example (a : Int) (P : Int → Prop) (h : P a) : P (a % 0) := by
  rw [Int.emod_zero]
  exact h

/-! ### R6. `simp` · closes `0 + a = a` (it uses `Int.zero_add`) -/
example (a : Int) : 0 + a = a := by
  simp

/-! ## `Int` → `Nat` -/

/-! ### R7. `Int.toNat` · `Int → Nat`, clamps negatives to `0`; `x.toNat = x` when `0 ≤ x` -/
example : (-2 : Int).toNat = 0 := by
  decide

/-! ### R8. `Int.natAbs` · `Int → Nat`, the absolute value `|x|` -/
example : (-3 : Int).natAbs = 3 := by
  decide

/-! ## Linear arithmetic with `/` and `%` by a literal -/

/-! ### R9. `omega` · closes linear goals over `Int`/`Nat`, including `/` and `%` by numerals
It treats `e / 2` as an unknown `q` with `2 * q ≤ e < 2 * q + 2` (floor semantics, as in R1). -/
example (k : Int) : (2 * k + 1) / 2 = k := by
  omega

/-! ## From an `Int` remainder to a `Nat` -/

/-! ### R10. `Int.emod_nonneg` · `(a : Int) {b : Int} : b ≠ 0 → 0 ≤ a % b` · context gains the fact
Supply the side condition for a literal `b` with `(by decide)`: `Int.emod_nonneg a (by decide)`. -/
example (a b : Int) (hb : b ≠ 0) (G : Prop) (g : 0 ≤ a % b → G) : G := by
  have h := Int.emod_nonneg a hb
  exact g h

/-! ### R11. `Int.toNat_of_nonneg` · `{a : Int} : 0 ≤ a → (a.toNat : Int) = a` · goal
`↑n` is a `Nat` cast back into `Int`. -/
example (a : Int) (ha : 0 ≤ a) (P : Int → Prop) (h : P a) : P (a.toNat : Int) := by
  rw [Int.toNat_of_nonneg ha]
  exact h

/-! ### R12. `unfold f` · goal: the name `f` applied to an argument → `f`'s body -/
def sqNat (n : Int) : Nat := (n * n).toNat

example (n : Int) (P : Nat → Prop) (h : P (n * n).toNat) : P (sqNat n) := by
  unfold sqNat
  exact h

/-! ### R13. `omega` knows `toNat` and casts `↑` between `Nat` and `Int` · closes the goal -/
example (a : Int) (h : 0 ≤ a) : (a.toNat : Int) = a := by
  omega

/-! ### R14. `decide` · evaluates a defined function on literals and closes the goal -/
example : sqNat (-3) = 9 := by
  decide

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The three conventions side by side on `-11` and `3` (R1, R2, R3) -/
example : (-11 : Int) / 3 = -4 ∧ (-11 : Int) % 3 = 1 ∧
    (-11 : Int).tdiv 3 = -3 ∧ (-11 : Int).tmod 3 = -2 := by
  decide

/-! ### W2. A negative odd numerator divided by 3, with `omega` (R9) -/
example (k : Int) : (-(3 * k + 1)) / 3 = -k - 1 := by
  omega

/-! ### W3. A `Nat`-valued last digit that is right for negative inputs (R12, R13, R14) -/
def lastDigit (n : Int) : Nat := (n % 10).toNat

example : lastDigit (-13) = 7 := by
  decide

example (n : Int) : (lastDigit n : Int) < 10 := by
  unfold lastDigit
  omega

/-! ### W4. `0 ≤ a % 10` from R10, then R11 turns `↑(a % 10).toNat` into `a % 10` -/
example (a : Int) (P : Int → Prop) (h : P (a % 10)) : P ((a % 10).toNat : Int) := by
  have h0 := Int.emod_nonneg a (by decide : (10 : Int) ≠ 0)
  rw [Int.toNat_of_nonneg h0]
  exact h

end E060Guide
