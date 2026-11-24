/- Guide for E083 (Bit vectors).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other widths, other numbers).
Assumed: Lean basics (E001–E033). No Mathlib: `BitVec` and `bv_omega` are in core Lean.
-/

namespace E083Guide

/-! # Part R · Reference entries -/

/-! ## Literals: evaluate, do not prove -/

/-! ### R1. `n#w` and `.toNat` · `decide` closes the goal
`BitVec w` is a w-bit word: a natural number below `2 ^ w`. `n#w` is the literal `n` taken mod
`2 ^ w` (`0x1F = 31`, and `31 mod 16 = 15`). `x.toNat : Nat` is its unsigned value. -/
example : (0x1F#4).toNat = 15 := by
  decide

/-! ### R2. Wraparound `+ - *` on literals · `decide` closes the goal
Arithmetic is mod `2 ^ w`: in 3 bits, `7 + 2 = 9 = 8 + 1`, and `0 - 1 = 7`. -/
example : 7#3 + 2#3 = 1#3 ∧ 0#3 - 1#3 = 7#3 := by
  decide

/-! ### R3. Shifts and bitwise ops on literals · `decide` closes the goal
`x <<< k`, `x >>> k` shift by a `Nat` `k` (bits pushed out are lost); `&&&`, `|||`, `^^^` are
bitwise and, or, xor. -/
example : 2#4 <<< 2 = 8#4 ∧ 9#4 <<< 1 = 2#4 ∧ (5#4 ^^^ 3#4) = 6#4 := by
  decide

/-! ## Bitwise identities on variables -/

/-! ### R4. `BitVec.xor_self` · `x ^^^ x = 0#w` · goal -/
example {w : Nat} (x : BitVec w) (P : BitVec w → Prop) (h : P 0#w) : P (x ^^^ x) := by
  rw [BitVec.xor_self]
  exact h

/-! ### R5. `simp` · closes a bitwise identity on a variable (it knows R4, `BitVec.and_self`, …) -/
example {w : Nat} (x : BitVec w) : x &&& x = x := by
  simp

/-! ## From `BitVec` to `Nat` -/

/-! ### R6. `BitVec.isLt` · `x.toNat < 2 ^ w` · context gains the bound -/
example {w : Nat} (x : BitVec w) (P : Prop) (g : x.toNat < 2 ^ w → P) : P := by
  have h := x.isLt
  exact g h

/-! ### R7. `BitVec.toNat_add` · `(x + y).toNat = (x.toNat + y.toNat) % 2 ^ w` · goal -/
example {w : Nat} (x y : BitVec w) (P : Nat → Prop) (h : P ((x.toNat + y.toNat) % 2 ^ w)) :
    P (x + y).toNat := by
  rw [BitVec.toNat_add]
  exact h

/-! ### R8. `BitVec.lt_def` · `x < y ↔ x.toNat < y.toNat` (unsigned) · context, with `at h` -/
example {w : Nat} (x y : BitVec w) (P : Prop) (h : x < y) (g : x.toNat < y.toNat → P) : P := by
  rw [BitVec.lt_def] at h
  exact g h

/-! ### R9. `BitVec.toNat_ofNat` · `(n#w).toNat = n % 2 ^ w` · goal -/
example (P : Nat → Prop) (h : P (5 % 2 ^ 8)) : P (5#8).toNat := by
  rw [BitVec.toNat_ofNat]
  exact h

/-! ## Closing linear facts -/

/-! ### R10. `omega` · closes linear `Nat`/`Int` goals, `%` and `/` by a numeral and `2 ^ 8` included -/
example (a b : Nat) (h : a + b < 2 ^ 8) : (a + b) % 2 ^ 8 = a + b := by
  omega

/-! ### R11. `bv_omega` · closes linear `BitVec` goals: R7–R9 (and friends) to `Nat`, then R10
Understands `+ - < ≤ = ≠`, `.toNat` and literals; not `&&& ||| ^^^` or shifts of variables. -/
example (x y : BitVec 8) (h1 : x ≤ y) (h2 : y < 20#8) : x ≠ 30#8 := by
  bv_omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A bound by hand at width 4: R6, then R10 -/
example (x : BitVec 4) : x.toNat < 16 := by
  have h := x.isLt
  omega

/-! ### W2. Doubling without overflow by hand: R7, then R10 -/
example (x : BitVec 8) (h : x.toNat < 128) : (x + x).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_add]
  omega

/-! ### W3. A hypothesis that rules out wraparound, all at once: R11
`x + 50#8 = 10#8` would need `x = 216`, which `h` excludes. -/
example (x : BitVec 8) (h : x < 200#8) : x + 50#8 ≠ 10#8 := by
  bv_omega

end E083Guide
