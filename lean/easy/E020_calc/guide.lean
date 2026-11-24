/- Guide for E020 (calc).
Part R: one reference entry per tactic or lemma the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`x y z w : Nat` are arbitrary natural numbers; `P : Nat → Prop` stands for "the rest of the goal":
the step changes only the part shown inside `P (…)`. A hypothesis `h` in an entry is only there to
finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E019, in particular `exact` (E003), `rw` (E009) and `omega` (E011).
-/

namespace E020Guide

/-! # Part R · Reference entries -/

/-! ## `calc` chains -/

/-! ### R1. `calc` with `=` steps · closes the goal `x = z`
Each line is `lhs = rhs := proof`. The first line names its left side (`x`); every later line starts
with `_`, which stands for the previous line's right side. The first left side and the last right
side must be the goal's two sides. A step's proof is any term (here a hypothesis) or a `by` block.
`calc` is also a term: `theorem t … := calc …` works without `by`. -/
example (x y z : Nat) (h1 : x = y) (h2 : y = z) : x = z := by
  calc x = y := h1
    _ = z := h2

/-! ### R2. `calc` mixing `≤` and `<` · closes the goal `x < z`
Two steps `x ≤ y` and `y < z` combine to `x < z`. The chain's relation is `<` as soon as one step is
`<`, `≤` when all steps are `≤`, and an `=` step keeps the other relation. Lean combines the steps with
`Trans` instances, which exist for these pairs. `y > z` is notation for `z < y`. -/
example (x y z : Nat) (h1 : x ≤ y) (h2 : y < z) : x < z := by
  calc x ≤ y := h1
    _ < z := h2

/-! ### R3. A step proved by `?_` · goal list: that step becomes the next goal
`?_` postpones the step's proof: after the `calc`, the step `x = y` is a goal of its own. This is
exactly the goal a `by` block in that step would start from. It needs tactic mode (`:= by calc …`):
in a term-mode `calc`, `?_` is the error "don't know how to synthesize placeholder". With several
`?_` steps the new goals are tagged `case calc_1`, `case calc_2`, … in chain order. -/
example (x y z : Nat) (h1 : x = y) (h2 : y = z) : x = z := by
  calc x = y := ?_
    _ = z := h2
  exact h1

/-! ## Inside one step: substitute, expand, collect -/

/-! ### R4. `rw [h1, h2]` · goal: substitutions applied left to right
`rw [h1, h2]` is `rw [h1]` then `rw [h2]` (shown here as two lines). With `h1 : x = y + z` the `x`
becomes `y + z`; only then does `h2 : z = y` find a `z` to replace. After the last rewrite `rw` tries
`rfl`, so an equation whose two sides became identical is closed on the spot. -/
example (P : Nat → Prop) (x y z : Nat) (h1 : x = y + z) (h2 : z = y) (h : P (y + y)) : P x := by
  rw [h1]
  rw [h2]
  exact h

/-! ### R5. `Nat.add_mul` · `(n + m) * k = n * k + m * k` · goal: distribute from the right -/
example (P : Nat → Prop) (x y z : Nat) (h : P (x * z + y * z)) : P ((x + y) * z) := by
  rw [Nat.add_mul]
  exact h

/-! ### R6. `Nat.mul_add` · `n * (m + k) = n * m + n * k` · goal: distribute from the left -/
example (P : Nat → Prop) (x y z : Nat) (h : P (x * y + x * z)) : P (x * (y + z)) := by
  rw [Nat.mul_add]
  exact h

/-! ### R7. `omega` with products · closes linear arithmetic in which `x * y` is one unknown
`omega` (E011) handles `+`, `-` and multiplication by a numeral. A product of two variables is an
*atom*: an unknown number, compared as written. So `x * y + x * y + x * y = 3 * (x * y)` is linear in
the atom `x * y`, but `y * x` is a different atom and `(x + y) * (x + y)` is one opaque atom too. -/
example (x y : Nat) : x * y + x * y + x * y = 3 * (x * y) := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A four-step chain `=`, `≤`, `<`, `≤` as a term (R1, R2): the result is `<` -/
example (x y z w v : Nat) (h1 : x = y) (h2 : y ≤ z) (h3 : z < w) (h4 : w ≤ v) : x < v :=
  calc x = y := h1
    _ ≤ z := h2
    _ < w := h3
    _ ≤ v := h4

/-! ### W2. R5 then R6 on `(q + 1) * (q + 1)`: `rw [Nat.mul_add]` rewrites only the first match
`Nat.mul_add` matches `q * (q + 1)` first and rewrites every copy of THAT product; `1 * (q + 1)` is a
different instance and stays. The last `rw` closes the goal by `rfl`. -/
example (q : Nat) : (q + 1) * (q + 1) = q * q + q * 1 + 1 * (q + 1) := by
  rw [Nat.add_mul]
  rw [Nat.mul_add]

/-! ### W3. Substitute, expand, collect, as one `calc` (R1, R4, R5, R6, R7) -/
example (p q : Nat) (h1 : p = q + 1) : p * p = q * q + 2 * q + 1 :=
  calc p * p = (q + 1) * (q + 1) := by rw [h1]
    _ = q * q + q * 1 + 1 * (q + 1) := by rw [Nat.add_mul, Nat.mul_add]
    _ = q * q + 2 * q + 1 := by omega

end E020Guide
