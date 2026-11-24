/- Guide for E033 (Library search).
Part R: one reference entry per tactic, command or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G` is any goal the step does not look at.
Part W: worked combinations on other statements (a length of an append, a chain of `<` and `≤`), not
on the exercise's.
Assumed: Lean basics up to E032 (`exact`/`apply` E003, term mode E004, `rw` E009, `have` E021,
implicit arguments `{…}` and `#check @L` E023, list library names E024).
-/

namespace E033Guide

/-! # Part R · Reference entries -/

/-! ## Searching the library -/

/-! ### R1. `exact?` · closes the goal and prints `Try this: exact …`; goal list loses the goal
`exact?` searches every lemma in scope for one whose conclusion matches the goal, filling its
hypotheses from the context. Click the suggestion (or copy it) to replace `exact?` by that line. -/
example (n : Nat) (h : n ≠ 0) : 0 < n := by
  exact?

/-! ### R2. `#check L` · changes nothing; prints `L`'s statement with its binders
Parentheses `(…)` are explicit arguments you write, braces `{…}` implicit ones Lean infers. -/
#check Nat.zero_lt_of_ne_zero

/-! ### R3. `apply L` (the form `apply?` suggests) · goal list: the goal → one goal per hypothesis of `L`
`Nat.mul_le_mul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂`.
`apply?` prints
`refine L ?_ ?_` lines like this, with the remaining subgoals as `-- ⊢ …` comments. -/
example (a b c d : Nat) (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := by
  apply Nat.mul_le_mul
  exact h₁
  exact h₂

/-! ## The lemmas the exercise needs -/

/-! ### R4. `List.length_reverse` · goal: `l.reverse.length` → `l.length`
`List.length_reverse {α : Type} {as : List α} : as.reverse.length = as.length`; all arguments
implicit, so the bare name is a proof of any instance. -/
example {α : Type} (l : List α) (P : Nat → Prop) (h : P l.length) : P l.reverse.length := by
  rw [List.length_reverse]
  exact h

/-! ### R5. `Nat.le_of_dvd` · context gains `h : m ≤ n`; goal unchanged
`Nat.le_of_dvd {m n : Nat} (h : 0 < n) : m ∣ n → m ≤ n`. The positivity proof comes FIRST, the
divisibility proof second. -/
example (m n : Nat) (hn : 0 < n) (hd : m ∣ n) (G : Prop) (g : m ≤ n → G) : G := by
  have h := Nat.le_of_dvd hn hd
  exact g h

/-! ### R6. `List.reverse_append` · goal: `(l ++ l').reverse` → `l'.reverse ++ l.reverse`
`List.reverse_append {α : Type} {as bs : List α} : (as ++ bs).reverse = bs.reverse ++ as.reverse`;
all arguments implicit. -/
example {α : Type} (l l' : List α) (P : List α → Prop) (h : P (l'.reverse ++ l.reverse)) :
    P (l ++ l').reverse := by
  rw [List.reverse_append]
  exact h

/-! ### R7. `Nat.mod_lt` · context gains `h : x % y < y`; goal unchanged
`Nat.mod_lt (x : Nat) {y : Nat} (hy : 0 < y) : x % y < y`. `y` is implicit because `hy`
determines it; `x` occurs in no hypothesis, so the library makes it explicit and you pass it first. -/
example (x y : Nat) (hy : 0 < y) (G : Prop) (g : x % y < y → G) : G := by
  have h := Nat.mod_lt x hy
  exact g h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Two library rewrites in a row: R4, then `List.length_append` (E024) -/
example {α : Type} (l l' : List α) : (l ++ l').reverse.length = l.length + l'.length := by
  rw [List.length_reverse]
  rw [List.length_append]

/-! ### W2. A lemma applied to arguments, used inside another lemma (term mode)
`Nat.lt_of_lt_of_le {n m k : Nat} : n < m → m ≤ k → n < k`; R7 supplies its first argument. -/
example (x y z : Nat) (hy : 0 < y) (hz : y ≤ z) : x % y < z :=
  Nat.lt_of_lt_of_le (Nat.mod_lt x hy) hz

/-! ### W3. `exact?` also finds lemmas that need several hypotheses from the context -/
example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  exact?

end E033Guide
