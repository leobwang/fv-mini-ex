/- Guide for M027 (Fast exponentiation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h…` in an entry is only there to finish the example; it shows what the goal became.
The case alternatives in R1 are written `| caseK … => ?_` so that every case stays open as a goal
you can inspect; in the exercise you write tactics after `=>` instead.
Part W: worked combinations on `walk` below and on other powers, not on the exercise's function.
Assumed: Lean basics (E001–E033). E084 (functional induction) helps but is not needed.
-/

namespace M027Guide

/-- The guide's recursive function, with the same branch shape as the exercise's:
`if e = 0 then … else (let r := recursive call; if e % 2 = 0 then r else …)`.
It halves `e` and bumps `a`; what it computes does not matter here. -/
def walk (a e : Nat) : Nat :=
  if e = 0 then a
  else
    let r := walk (a + 1) (e / 2)
    if e % 2 = 0 then r else a + r
termination_by e

/-! # Part R · Reference entries -/

/-! ## Splitting along the function's branches -/

/-! ### R1. `fun_induction walk a e with | case1 … | case2 … | case3 …` · goal list: one goal per branch
`case1` is `e = 0` (with `e` replaced by `0`), `case2` the even branch, `case3` the odd branch. Each
arm names, in order: the arguments (`a e`; `case1` has only `a`, since `e` became `0`), the condition
`he : ¬e = 0`, the `let` variable `r` (a local definition `r : Nat := …`), the parity condition `h2`,
and the IH `ih`, which is the goal for the recursive call's arguments `(a + 1, e / 2)`. -/
example (P : Nat → Nat → Nat → Prop) (h0 : ∀ a, P a 0 a)
    (hev : ∀ a e, P (a + 1) (e / 2) (walk (a + 1) (e / 2)) → P a e (walk (a + 1) (e / 2)))
    (hodd : ∀ a e, P (a + 1) (e / 2) (walk (a + 1) (e / 2)) → P a e (a + walk (a + 1) (e / 2)))
    (a e : Nat) : P a e (walk a e) := by
  fun_induction walk a e with
    | case1 a => ?_
    | case2 a e he r h2 ih => ?_
    | case3 a e he r h2 ih => ?_
  · exact h0 a
  · exact hev a e ih
  · exact hodd a e ih

/-! ## The base case -/

/-! ### R2. `Nat.pow_zero` · `n ^ 0 = 1` · goal: `a ^ 0` → `1`
`simp` applies it by itself, so `simp` closes `1 = a ^ 0` outright. -/
example (a : Nat) (P : Nat → Prop) (h : P 1) : P (a ^ 0) := by
  rw [Nat.pow_zero]
  exact h

/-! ## The recursive cases -/

/-! ### R3. `show G'` · goal: a `let` variable replaced by its value
`r : Nat := f x` is a local definition: `r` *is* `f x` by definition, so `show` accepts the goal with
`f x` written in place of `r`. `rw` cannot see through `r`; after `show` it can (`rw [ih]`). -/
example (f : Nat → Nat) (x : Nat) (P : Nat → Prop) (h : P (f x)) : let r := f x; P r := by
  intro r
  show P (f x)
  exact h

/-! ### R4. `Nat.pow_two` · `a ^ 2 = a * a`; right to left, `rw [← Nat.pow_two]` turns `a * a` into `a ^ 2` -/
example (a : Nat) (P : Nat → Prop) (h : P (a ^ 2)) : P (a * a) := by
  rw [← Nat.pow_two]
  exact h

/-! ### R5. `Nat.pow_mul` · `a ^ (m * n) = (a ^ m) ^ n`; right to left merges a power of a power -/
example (a m n : Nat) (P : Nat → Prop) (h : P (a ^ (m * n))) : P ((a ^ m) ^ n) := by
  rw [← Nat.pow_mul]
  exact h

/-! ### R6. `congr 1` · goal: `a ^ x = a ^ y` → `x = y` (equal exponents suffice)
It also makes `a = a` for the bases, which it closes by `rfl` itself. The new goal is named `e_a`. -/
example (a x y : Nat) (h : y = x) : a ^ x = a ^ y := by
  congr 1
  exact h.symm

/-! ### R7. `omega` · closes linear arithmetic over `Nat`, including `/` and `%` by a numeral
It knows `n = 2 * (n / 2) + n % 2`, and reads `k.succ` as `k + 1`. -/
example (n : Nat) (h : n % 2 = 0) : 2 * (n / 2) = n := by omega

example (n : Nat) (h : ¬n % 2 = 0) : (2 * (n / 2)).succ = n := by omega

/-! ### R8. `Nat.pow_succ'` · `m ^ n.succ = m * m ^ n`; right to left absorbs a factor `m` into the power
`n.succ` is `n + 1` (the constructor `Nat.succ`); the goal prints it as `n.succ`. -/
example (m n : Nat) (P : Nat → Prop) (h : P (m ^ n.succ)) : P (m * m ^ n) := by
  rw [← Nat.pow_succ']
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `fun_induction` on `walk`, `show` in the recursive cases, `omega` everywhere: R1, R3, R7 -/
example (a e : Nat) : a ≤ walk a e := by
  fun_induction walk a e with
    | case1 a => omega
    | case2 a e he r h2 ih =>
      show a ≤ walk (a + 1) (e / 2)
      omega
    | case3 a e he r h2 ih =>
      show a ≤ a + walk (a + 1) (e / 2)
      omega

/-! ### W2. Collapse a tower of powers into one power, then compare exponents: R4, R5, R5, R6, R7 -/
example (c k : Nat) : ((c * c) ^ k) ^ 2 = c ^ (4 * k) := by
  rw [← Nat.pow_two c]
  rw [← Nat.pow_mul]
  rw [← Nat.pow_mul]
  congr 1
  omega

/-! ### W3. Absorb a lone factor, then compare exponents: R8, R6, R7 -/
example (c k : Nat) : c * c ^ (k + k) = c ^ (2 * k + 1) := by
  rw [← Nat.pow_succ']
  congr 1
  omega

end M027Guide
