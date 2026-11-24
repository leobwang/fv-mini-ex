/- Guide for E010 (simp).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries R2, R3, R5, R7 use `simp only [lemma]` so that exactly one lemma fires; plain `simp` uses all
of them (and many more) at once.
Part W: worked combinations on `double`, `triple` and `List.reverse`, not on the exercise's `square`.
Assumed: Lean basics up to E009: `rfl` (E001), `def` (E002), `exact` (E003), `rw`, `rw … at h` and the
lemmas `Nat.add_zero`, `Nat.add_comm`, `List.length_append` (E009).
-/

namespace E010Guide

/-- `double n = n + n`: a definition of our own, so it is NOT in the default simp set. -/
def double (n : Nat) : Nat := n + n

/-- `triple n = n + n + n`, used in Part W. -/
def triple (n : Nat) : Nat := n + n + n

/-! # Part R · Reference entries -/

/-! ## The default simp set -/

/-! ### R1. `simp` · goal: rewritten with every `@[simp]` lemma until nothing applies; closed if it
becomes `True` or both sides become syntactically equal (then `rfl` finishes it)
The default simp set already contains `List.nil_append : [] ++ as = as`, `List.append_nil`,
`List.length_append`, `Nat.add_zero`, `Nat.mul_one`, … (R2–R7). -/
example {α : Type} (xs : List α) : ([] ++ xs).length = xs.length := by
  simp

/-! ### R2. `List.append_nil` · `as ++ [] = as` · goal: `xs ++ []` → `xs` -/
example {α : Type} (xs : List α) (P : List α → Prop) (h : P xs) : P (xs ++ []) := by
  simp only [List.append_nil]
  exact h

/-! ### R3. `List.length_append` · `(as ++ bs).length = as.length + bs.length` · goal: length of an
append → sum of lengths -/
example {α : Type} (xs ys : List α) (P : Nat → Prop) (h : P (xs.length + ys.length)) :
    P (xs ++ ys).length := by
  simp only [List.length_append]
  exact h

/-! ## Unfolding your own definitions -/

/-! ### R4. `simp [f]` · goal: the defined name `f` → its body
Plain `simp` does not unfold a `def` you wrote; on `P (double k)` it fails with
"simp made no progress". Passing the name `double` adds its defining equation
`double n = n + n` to the simp set. -/
example (k : Nat) (P : Nat → Prop) (h : P (k + k)) : P (double k) := by
  simp [double]
  exact h

/-! ### R5. `Nat.add_zero` · `n + 0 = n` · goal: `n + 0` → `n` (in the default simp set) -/
example (n : Nat) (P : Nat → Prop) (h : P n) : P (n + 0) := by
  simp only [Nat.add_zero]
  exact h

/-! ## Simplifying a hypothesis -/

/-! ### R6. `simp at h` · context: `h` is simplified; goal unchanged
Same lemmas as `simp`, applied to the hypothesis `h` instead of the goal. If `h` becomes `False`,
the goal is closed. -/
example (n : Nat) (P : Nat → Prop) (h : P (n * 1)) : P n := by
  simp at h
  exact h

/-! ### R7. `Nat.mul_one` · `n * 1 = n` · goal: `n * 1` → `n` (in the default simp set) -/
example (n : Nat) (P : Nat → Prop) (h : P n) : P (n * 1) := by
  simp only [Nat.mul_one]
  exact h

/-! ### R8. `exact h` · closes a goal that is exactly the statement of `h` (E003) -/
example (G : Prop) (h : G) : G := by
  exact h

/-! ## Rewriting with a hypothesis -/

/-! ### R9. `simp [hf]` with `hf : ∀ x, f x = e x` · goal: every `f t` → `e t`, inner ones too
A hypothesis in the list is used like a lemma, left to right, for every value of `x`; `simp` repeats
it, so the nested `f (f a)` is rewritten twice. (`rw [hf]` rewrites only one pattern at a time.) -/
example (f : Nat → Nat) (a : Nat) (hf : ∀ x, f x = 2 * x) (P : Nat → Prop)
    (h : P (2 * (2 * a))) : P (f (f a)) := by
  simp [hf]
  exact h

/-! ## Closing arithmetic equations -/

/-! ### R10. `Nat.add_right_cancel_iff` · `m + n = k + n ↔ m = k` · goal: cancel a common summand on
the right
A literal is split as needed: `b + 2` matches `(b + 1) + 1`, so the common `+ 1` cancels. `simp` uses
an `↔` lemma to rewrite the whole proposition `m + n = k + n` into `m = k`. -/
example (a b : Nat) (h : a = b + 1) : a + 1 = b + 2 := by
  simp only [Nat.add_right_cancel_iff]
  exact h

/-! ### R11. `simp` closes `n + 1 + 1 + 1 = n + 3` · goal closed
R10 cancels `+ 1` on the right twice until `n + 1 = n + 1` is left; `Nat.add_left_cancel_iff`
(`n + m = n + k ↔ m = k`) cancels the `n` on the left, leaving `1 = 1`, and
`eq_self : (a = a) = True` closes it. `simp` does NOT rewrite `n + 1 + 1` to `n + 2` inside a
larger term `P (n + 1 + 1)`: there it makes no progress. -/
example (n : Nat) : n + 1 + 1 + 1 = n + 3 := by
  simp

/-! # Part W · Worked combinations (on `double`, `triple`, `reverse`, not the exercise's objects) -/

/-! ### W1. `simp` leaves what it cannot finish: it does not reorder a sum. R1 + R3, then E009 -/
example {α : Type} (xs ys : List α) : ([] ++ xs ++ ys).length = (ys ++ xs).length := by
  simp
  rw [Nat.add_comm]

/-! ### W2. Unfold your definition and clean up its argument in one call: R4 + R7 -/
example (n : Nat) : triple (n * 1) = n + n + n := by
  simp [triple]

/-! ### W3. Clean up a hypothesis, then use it: R6 (with R5, R7 inside), then R8 -/
example (a b : Nat) (h : 0 + a * 1 = b) : a = b := by
  simp at h
  exact h

/-! ### W4. A hypothesis about a function, used twice by one `simp`: R9, then `simp` computes `1 + 3 + 3` to `7` -/
example (g : Nat → Nat) (hg : ∀ x, g x = x + 3) : g (g 1) = 7 := by
  simp [hg]

/-! ### W5. Several names at once: definitions and hypotheses mix freely: R4 + R9 -/
example (f : Nat → Nat) (hf : ∀ x, f x = x * 1) (k : Nat) : double (f k) = k + k := by
  simp [double, hf]

end E010Guide
