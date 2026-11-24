/- Guide for E009 (Rewriting).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `k` in an entry is only there to finish the example; it shows what the goal became.
The one fact behind every entry: `rw [e]` with `e : l = r` finds the term `l` in the goal (or in a
hypothesis, with `at`) and replaces it by `r`, then tries to close the goal with `rfl`.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E008 (`theorem`, `example`, `intro`, `exact`, `rfl`, `∧`, `∨`, `¬`).
-/

namespace E009Guide

/-! # Part R · Reference entries -/

/-! ## Rewriting with a hypothesis -/

/-! ### R1. `rw [h]` with `h : a = b` · goal: every `a` → `b`
The left side `a` must occur in the goal exactly as written (up to instances). -/
example {α : Type} (a b : α) (P : α → Prop) (h : a = b) (k : P b) : P a := by
  rw [h]
  exact k

/-! ### R2. `rw [h₁, h₂]` · goal: rewrite with `h₁`, then with `h₂`, left to right
Same as `rw [h₁]` followed by `rw [h₂]`; `h₂` sees the goal `h₁` produced. -/
example {α : Type} (a b c d : α) (P : α → α → Prop) (h₁ : a = b) (h₂ : c = d) (k : P b d) :
    P a c := by
  rw [h₁, h₂]
  exact k

/-! ### R3. `rw` closes `t = t` by itself · goal list: the goal disappears
After the last rewrite, `rw` tries `rfl`. If both sides are now the same text, the goal is closed
and a following `rfl` or `exact` would be an error ("no goals"). -/
example {α β : Type} (f : α → β) (a b : α) (h : a = b) : f a = f b := by
  rw [h]

/-! ### R4. `rw [← h]` with `h : a = b` · goal: every `b` → `a` (right to left) -/
example {α : Type} (a b : α) (P : α → Prop) (h : a = b) (k : P a) : P b := by
  rw [← h]
  exact k

/-! ### R5. `rw [h] at k` · context: hypothesis `k` rewritten; goal unchanged -/
example {α : Type} (a b : α) (P : α → Prop) (h : a = b) (k : P a) : P b := by
  rw [h] at k
  exact k

/-! ## Rewriting with library equations -/

/-! ### R6. `Nat.add_zero : ∀ (n : Nat), n + 0 = n` · here used `at` a hypothesis
`rw [Nat.add_zero] at k`: Lean picks `n` itself from the first `_ + 0` it finds in `k`. -/
example (n : Nat) (P : Nat → Prop) (k : P (n + 0)) : P n := by
  rw [Nat.add_zero] at k
  exact k

/-! ### R7. `List.length_append : (as ++ bs).length = as.length + bs.length` · goal
`as ++ bs` is list concatenation; `xs.length` is `List.length xs`. -/
example {α : Type} (as bs : List α) (P : Nat → Prop) (k : P (as.length + bs.length)) :
    P (as ++ bs).length := by
  rw [List.length_append]
  exact k

/-! ### R8. `Nat.add_comm : ∀ (n m : Nat), n + m = m + n` with no arguments · goal
`rw` fixes `n, m` from the FIRST sum it meets, then rewrites every copy of that one sum only.
Here `a + b` is met first; `c + d` is a different sum and stays. -/
example (a b c d : Nat) (P : Nat → Nat → Prop) (k : P (b + a) (c + d)) : P (a + b) (c + d) := by
  rw [Nat.add_comm]
  exact k

/-! ### R9. `Nat.add_comm c d` with explicit arguments · goal: only the sum `c + d` flips -/
example (a b c d : Nat) (P : Nat → Nat → Prop) (k : P (a + b) (d + c)) : P (a + b) (c + d) := by
  rw [Nat.add_comm c d]
  exact k

/-! ## Closing what `rw` leaves open -/

/-! ### R10. `rfl` · closes `[x].length + n = 1 + n`, which `rw`'s own `rfl` does not
`rw` tries `rfl` with only "reducible" definitions unfolded; `List.length` is not one of them. The
`rfl` tactic unfolds it: `[x].length` computes to `1`. `[x]` is the one-element list. -/
example {α : Type} (x : α) (n : Nat) : [x].length + n = 1 + n := by
  rfl

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. A chain of hypotheses (R2), closed by `rw` itself (R3) -/
example (x y z : Nat) (h₁ : x = y * 2) (h₂ : z = y) : x = z * 2 := by
  rw [h₁, h₂]

/-! ### W2. A rewrite list at a hypothesis (R5, R6), then `exact` -/
example (n m : Nat) (P : Nat → Prop) (h : n = m) (k : P (n + 0)) : P m := by
  rw [Nat.add_zero, h] at k
  exact k

/-! ### W3. A library rewrite leaves a goal that only `rfl` closes (R7, R10) -/
example {α : Type} (as : List α) (x : α) : (as ++ [x]).length = as.length + 1 := by
  rw [List.length_append]
  rfl

/-! ### W4. `Nat.add_comm` without arguments flips the OUTER sum first (R8); name the inner one (R9)
`a + (b + c)` is the sum `a + s` with `s = b + c`, and it is met before `b + c` itself. -/
example (a b c : Nat) (k : b + c + a = a + (c + b)) : a + (b + c) = a + (c + b) := by
  rw [Nat.add_comm]
  exact k

example (a b c : Nat) : a + (b + c) = a + (c + b) := by
  rw [Nat.add_comm b c]

end E009Guide
