/- Guide for M142 (The CHSH operator identity).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`R` is any ring (`[Ring R]`): `+`, `-`, `*`, `0`, `1` with the usual laws, except that `*` need not
commute. `ℤ`, `ℝ`, `ℂ` and the square matrices `Matrix n n ℂ` are rings.
Part W: worked combinations on objects that are NOT the exercise's (a right-cancelling helper, the
operator `a * b + b * a` instead of the CHSH operator).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace M142Guide

/-! # Part R · Reference entries -/

/-! ## Helpers that rewrite inside a word -/

/-! ### R1. `have name : ∀ {a b : R}, … := by …` · context gains a reusable helper
Braces `{a}` make `a` implicit: `one_l ha` reads `a` off `ha : a = 1` and is the equation
`∀ x, a * x = x`. The proof lines after `:= by` must be indented further than `have`.
(This helper is not one the exercise needs; its shape is the same.) -/
example {R : Type} [Ring R] (G : Prop)
    (k : (∀ {a : R}, a = 1 → ∀ x, a * x = x) → G) : G := by
  have one_l : ∀ {a : R}, a = 1 → ∀ x, a * x = x := by
    intro a h x
    rw [h, one_mul]
  exact k one_l

/-! ### R2. `intro a b h x` · context gains the binders, goal becomes the body
`intro` also names implicit binders `{a b}`. Lean prints `∀ x, …` as `∀ (x : R), …`. -/
example {R : Type} [Ring R] (Q : R → R → R → Prop) (k : ∀ a b x : R, Q a b x) :
    ∀ {a b : R}, a * b = b * a → ∀ x, Q a b x := by
  intro a b h x
  exact k a b x

/-! ### R3. `rw [← mul_assoc]` · `mul_assoc : a * b * c = a * (b * c)`; right to left
groups the first `a * (b * c)` it finds to the left (`a * b * c` means `(a * b) * c`) -/
example {R : Type} [Ring R] (a b c : R) (P : R → Prop) (h : P (a * b * c)) : P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R4. `rw [mul_assoc]` · goal: the first `a * b * c` → `a * (b * c)` -/
example {R : Type} [Ring R] (a b c : R) (P : R → Prop) (h : P (a * (b * c))) : P (a * b * c) := by
  rw [mul_assoc]
  exact h

/-! ### R5. `one_mul` · `1 * a = a` · goal -/
example {R : Type} [Ring R] (a : R) (P : R → Prop) (h : P a) : P (1 * a) := by
  rw [one_mul]
  exact h

/-! ## Normalising both sides -/

/-! ### R6. `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]` · goal: the numeral `4` → `1 + 1 + 1 + 1`
`show T by tac` is a term proving `T`; `rw` then uses it like a lemma. `norm_num` proves numeral
identities in any ring. -/
example {R : Type} [Ring R] (P : R → Prop) (h : P (1 + 1 + 1 + 1)) : P 4 := by
  rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
  exact h

/-! ### R7. `sq` · `a ^ 2 = a * a` · goal (`simp only [sq]` rewrites every square) -/
example {R : Type} [Ring R] (a : R) (P : R → Prop) (h : P (a * a)) : P (a ^ 2) := by
  simp only [sq]
  exact h

/-! ### R8. `simp only [add_mul, mul_add, sub_mul, mul_sub]` · goal: products distributed over `+`, `-`
`add_mul : (a + b) * c = a * c + b * c`, `mul_add : a * (b + c) = a * b + a * c`, and the same for `-`.
The order of factors is kept: nothing here needs `*` to commute. -/
example {R : Type} [Ring R] (a b c d : R) (P : R → Prop)
    (h : P (a * c + b * c - (a * d + b * d) - (a * c - b * c + (a * d - b * d)))) :
    P ((a + b) * (c - d) - (a - b) * (c + d)) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  exact h

/-! ### R9. `simp only [mul_assoc]` · goal: every product re-associated to the right -/
example {R : Type} [Ring R] (a b c d : R) (P : R → Prop) (h : P (a * (b * (c * d)))) :
    P (a * b * c * d) := by
  simp only [mul_assoc]
  exact h

/-! ### R10. `simp only [sw hab]` · goal: `b` and `a` swapped inside a right-nested word
`sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x)`, so `sw hab` is the rewrite rule
`∀ x, b * (a * x) = a * (b * x)`: it fires on `b * (a * _)` at any depth. -/
example {R : Type} [Ring R] (a b c x : R) (P : R → Prop)
    (sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x))
    (hab : a * b = b * a) (h : P (c * (a * (b * x)))) : P (c * (b * (a * x))) := by
  simp only [sw hab]
  exact h

/-! ### R11. `simp only [sq1 ha]` · goal: a square in front of a tail cancels, `a * (a * x)` → `x` -/
example {R : Type} [Ring R] (a c x : R) (P : R → Prop)
    (sq1 : ∀ {a : R}, a * a = 1 → ∀ x, a * (a * x) = x)
    (ha : a * a = 1) (h : P (c * x)) : P (c * (a * (a * x))) := by
  simp only [sq1 ha]
  exact h

/-! ### R12. `simp only [ha]` (`ha : a * a = 1`) · goal: a square at the END of a word → `1` -/
example {R : Type} [Ring R] (a c : R) (P : R → Prop) (ha : a * a = 1) (h : P (c * 1)) :
    P (c * (a * a)) := by
  simp only [ha]
  exact h

/-! ### R13. `simp only [mul_one]` · `a * 1 = a` · goal -/
example {R : Type} [Ring R] (c : R) (P : R → Prop) (h : P c) : P (c * 1) := by
  simp only [mul_one]
  exact h

/-! ### R14. `abel` · closes an equation of sums and differences (additive commutative group),
treating each product such as `a * (b * c)` as an opaque atom, the numeral `1` included -/
example {R : Type} [Ring R] (x y : R) : 1 + x - y + (1 + y) = 1 + 1 + x := by
  abel

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R2, R4, `rw [h]`, R13: a helper that cancels a square on the RIGHT -/
example {R : Type} [Ring R] : ∀ {a : R}, a * a = 1 → ∀ x, x * a * a = x := by
  intro a h x
  rw [mul_assoc]
  rw [h]
  rw [mul_one]

/-! ### W2. R6–R12, R14 on `(ab + ba)² = 4` for commuting involutions `a`, `b`
(`a * a = 1`, `b * b = 1`, `a * b = b * a`). The helpers `sw`, `sq1` are given here as hypotheses
(in the exercise you prove them with R1–R5). Expand, re-associate, swap and cancel, then `abel`. -/
example {R : Type} [Ring R] (a b : R) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x))
    (sq1 : ∀ {a : R}, a * a = 1 → ∀ x, a * (a * x) = x) :
    (a * b + b * a) ^ 2 = 4 := by
  rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
  simp only [sq]
  simp only [add_mul, mul_add]
  simp only [mul_assoc]
  simp only [sw hab, sq1 ha, sq1 hb, ha, hb]
  abel

end M142Guide
