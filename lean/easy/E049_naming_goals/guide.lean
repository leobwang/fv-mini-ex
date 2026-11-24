/- Guide for E049 (Naming goals).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Names ending in `✝` (`n✝`, `a✝`, `a✝¹`) are inaccessible: Lean made them up, prints them, and you cannot
type them. The entries show how such names arise and how to replace them by names you choose.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace E049Guide

/-! # Part R · Reference entries -/

/-! ## Splitting a `Nat` and picking a goal by its tag -/

/-! ### R1. `cases n` (no names given) · goal list: one goal → goals tagged `zero` and `succ`
The `succ` goal gets a new variable that Lean calls `n✝`; you cannot write `n✝` in a tactic. -/
example (P : Nat → Prop) (h0 : P 0) (h : ∀ m, P (m + 1)) (n : Nat) : P n := by
  cases n
  exact h0
  exact h _

/-! ### R2. `case tag x => tac` · goal list: focus the goal tagged `tag`, name its `✝` variables `x`
`tac` must close that goal (or `case` fails). The tags need not be taken in order. -/
example (P : Nat → Prop) (h0 : P 0) (h : ∀ m, P (m + 1)) (n : Nat) : P n := by
  cases n
  case succ m => exact h m
  case zero => exact h0

/-! ### R3. `Or.inl`, `Or.inr` · closes `A ∨ B` from a proof of `A` (left) or of `B` (right) -/
example (A B : Prop) (a : A) : A ∨ B := by
  exact Or.inl a

example (A B : Prop) (b : B) : A ∨ B := by
  exact Or.inr b

/-! ### R4. `Nat.le_add_left` · `Nat.le_add_left (n m : Nat) : n ≤ m + n` · closes the goal
Both arguments are explicit: `Nat.le_add_left a k : a ≤ k + a`. -/
example (a k : Nat) : a ≤ k + a := by
  exact Nat.le_add_left a k

/-! ## Unnamed hypotheses -/

/-! ### R5. `intros` · context gains one `a✝` per premise; goal loses the premises
The most recent hypothesis is `a✝`, the one before it `a✝¹`, then `a✝²`, … -/
example (A B C : Prop) (h : A → B → C) : A → B → C := by
  intros
  exact h ‹A› ‹B›

/-! ### R6. `rename_i x y` · context: the LAST two inaccessible hypotheses become `x`, `y` (in order)
With fewer names than `✝`s, only the most recent ones are renamed: `rename_i y` names `a✝` only. -/
example (A B C : Prop) (h : A → B → C) : A → B → C := by
  intros
  rename_i x y
  exact h x y

example (A B C : Prop) (h : A → B → C) : A → B → C := by
  intros
  rename_i y
  exact h ‹A› y

/-! ## Splitting a `Bool` -/

/-! ### R7. `cases b` on `b : Bool` · goal list: goals `false` and `true`; context: every hypothesis
that mentions `b` is rewritten with the value (here `h`). -/
example (P : Bool → Prop) (x : Bool) (h : (!x) = true) (h0 : P false) (h1 : P true) :
    P x := by
  cases x
  exact h0
  exact h1

/-! ### R8. `next => tac` · goal list: focus the FIRST remaining goal, whatever its tag; `tac` closes it
`next x y => tac` also names that goal's `✝` variables, like `case`. -/
example (P : Bool → Prop) (x : Bool) (h0 : P false) (h1 : P true) : P x := by
  cases x
  next => exact h0
  next => exact h1

/-! ### R9. `nomatch h` · closes any goal when `h : false = true`
No constructor of `Eq` can produce `false = true`, so there are no cases to prove. It also works when
`h` only computes to `false = true`, e.g. `h : (!true) = true`. -/
example (P : Prop) (h : false = true) : P := by
  nomatch h

example (P : Prop) (h : (!true) = true) : P := by
  nomatch h

/-! ## Induction without names -/

/-! ### R10. `induction n` (no names) · goal list: goals `zero` and `succ`
The `succ` goal gets the variable `n✝` and the induction hypothesis `a✝ : P n✝`. -/
example (P : Nat → Prop) (z : P 0) (s : ∀ m, P m → P (m + 1)) (n : Nat) : P n := by
  induction n
  exact z
  exact s _ ‹_›

/-! ### R11. `case succ m ih => tac` · names the variable `m` and the induction hypothesis `ih`
The names are given in the order the `✝`s were made: the variable first, then the hypothesis. -/
example (P : Nat → Prop) (z : P 0) (s : ∀ m, P m → P (m + 1)) (n : Nat) : P n := by
  induction n
  case zero => exact z
  case succ m ih => exact s m ih

/-! ### R12. `Nat.add_succ` · `n + succ m = succ (n + m)`; `succ m` also matches `m + 1` · goal -/
example (a b : Nat) (P : Nat → Prop) (h : P (a + b).succ) : P (a + (b + 1)) := by
  rw [Nat.add_succ]
  exact h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. `case tag x =>` is "focus that goal, then `rename_i x`": the state inside the block
After `cases n` and the `zero` case, `rename_i m` shows the state `case succ m =>` starts from. -/
example (P : Nat → Prop) (h0 : P 0) (h : ∀ m, P (m + 1)) (n : Nat) : P n := by
  cases n
  case zero => exact h0
  rename_i m
  exact h m

/-! ### W2. The same for `induction`: `rename_i m ih` gives the state `case succ m ih =>` starts from -/
example (P : Nat → Prop) (z : P 0) (s : ∀ m, P m → P (m + 1)) (n : Nat) : P n := by
  induction n
  case zero => exact z
  rename_i m ih
  exact s m ih

/-! ### W3. `cases n` + `case` + an `∨`: R1, R2, R3, R4 -/
example (n : Nat) : n = 0 ∨ 3 ≤ n + 2 := by
  cases n
  case zero => exact Or.inl rfl
  case succ k => exact Or.inr (Nat.le_add_left 3 k)

/-! ### W4. Three premises: `intros`, then `rename_i` in the order they were introduced (R5, R6) -/
example (A B C : Prop) : A → B → (A → B → C) → C := by
  intros
  rename_i a b f
  exact f a b

/-! ### W5. `cases` on a `Bool` with an impossible branch: R7, R8, R9 -/
example (x : Bool) (h : (x && false) = true) : x = false := by
  cases x
  next => rfl
  next => nomatch h

/-! ### W6. `induction`, name `k ih`, rewrite with `Nat.add_succ` then `ih` (R10, R11, R12)
Written with `rename_i k ih` (W2) so each step shows its state here; inside `case succ k ih =>` the
states are the same. `rw` tries `rfl` after rewriting, which closes `(k + 2).succ = k + 1 + 2`. -/
example (n : Nat) : 2 + n = n + 2 := by
  induction n
  case zero => rfl
  rename_i k ih
  rw [Nat.add_succ]
  rw [ih]

/-! ### W7. The same proof with `case`: what the exercise's style looks like -/
example (n : Nat) : 2 + n = n + 2 := by
  induction n
  case zero => rfl
  case succ k ih => rw [Nat.add_succ, ih]

end E049Guide
