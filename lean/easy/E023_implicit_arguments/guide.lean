/- Guide for E023 (Implicit arguments).
Part R: one reference entry per way of passing (or not passing) an argument, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`L` below is the core lemma `Nat.lt_of_lt_of_le : ∀ {n m k : Nat}, n < m → m ≤ k → n < k`. Its
arguments in curly braces `{n m k}` are *implicit*: Lean fills them in. The two premises after the
comma (proofs of `n < m` and `m ≤ k`) are *explicit*: you write them. `P : α → Prop` stands for "the rest
of the goal". A hypothesis `k` in an entry is only there to finish the example.
Part W: worked combinations on lemmas and functions that are NOT the exercise's.
Assumed: E001–E022 (in particular `exact`/`apply` from E003, term mode from E004, `rw` from E009,
`have` from E021).
-/

namespace E023Guide

/-! # Part R · Reference entries -/

/-! ## Using a lemma with implicit arguments -/

/-! ### R1. `exact L h1 h2` · closes the goal; implicit arguments inferred from `h1`, `h2`
You pass only the explicit arguments. Lean reads `n m k` off their types: `h1 : a < b` forces
`n := a, m := b`, and `h2 : b ≤ c` forces `k := c`. -/
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  exact Nat.lt_of_lt_of_le h1 h2

/-! ### R2. `apply L (m := b)` · goal list: `a < c` → `a < b`, `b ≤ c`
`(m := b)` is a *named argument*: it sets the argument whose binder is called `m`, implicit or not,
and leaves the others to inference. The binder names are the ones `#check @L` prints. Without
`(m := b)`, `apply` cannot know `m` from the goal `a < c` alone (W1). -/
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  apply Nat.lt_of_lt_of_le (m := b)
  exact h1
  exact h2

/-! ### R3. `exact @L a b c h1 h2` · closes the goal; `@` makes every argument explicit
After `@`, the implicit arguments are written in order like the explicit ones: `n, m, k`, then the two
proofs. An argument you still want inferred can be written `_`: `@L _ b _ h1 h2`. -/
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  exact @Nat.lt_of_lt_of_le a b c h1 h2

/-! ### R4. `exact @L` · closes a `∀`-goal that is exactly `L`'s statement with explicit binders
`@L` with no arguments is a function of all of them: its type is `∀ (n m k : Nat), n < m → m ≤ k → n < k`,
with `(…)` where `L` has `{…}`. Plain `L` would instead try to fill `n m k` from the goal at once. -/
example : ∀ (n m k : Nat), n < m → m ≤ k → n < k := by
  exact @Nat.lt_of_lt_of_le

/-! ## Hypotheses with implicit binders -/

/-! ### R5. `have k := @h a` (`h : ∀ {x : α}, P x`) · context gains `k : P a`
A hypothesis can have an implicit binder too. `h` alone means "`h` at some `x` to be inferred";
`@h a` fixes `x := a`. `h (x := a)` does the same by name. -/
example {α : Type} (P : α → Prop) (h : ∀ {x : α}, P x) (a : α) : P a := by
  have k := @h a
  exact k

/-! ## Equations: apply a function, chain two -/

/-! ### R6. `congrArg g e` · from `e : x = y` get `g x = g y`; here: context gains it
`congrArg : ∀ {α β} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂`. The function is explicit, the
two sides are implicit (read off `e`). -/
example {α β : Type} (g : α → β) (x y : α) (e : x = y) : g x = g y := by
  have k := congrArg g e
  exact k

/-! ### R7. `exact e1.trans e2` (`Eq.trans`) · closes `x = z` from `e1 : x = y`, `e2 : y = z`
`Eq.trans : ∀ {α} {a b c : α}, a = b → b = c → a = c`: all of `α a b c` are implicit. `e1.trans e2`
is *dot notation*: `e1` has type `Eq …`, so `e1.trans` means `Eq.trans e1`. -/
example {α : Type} (x y z : α) (e1 : x = y) (e2 : y = z) : x = z := by
  exact e1.trans e2

/-! ### R8. `rw [@h a]` (`h : ∀ {x : α}, f x = x`) · goal: `f a` → `a`
`@h a : f a = a`, and `rw` rewrites every `f a` in the goal. (Plain `rw [h]` also works: `rw` picks `x`
from the first `f _` it finds, reading the goal from the outside in.) -/
example {α : Type} (f : α → α) (h : ∀ {x : α}, f x = x) (a : α) (P : α → Prop) (k : P a) :
    P (f a) := by
  rw [@h a]
  exact k

/-! # Part W · Worked combinations (not the exercise's lemmas) -/

/-! ### W1. `apply L` without a name: the middle argument becomes a hole `?m`
The goal `a < c` fixes `n := a` and `k := c` but says nothing about `m`. `apply` leaves goals
`a < ?m`, `?m ≤ c` (and a goal `Nat` for `?m` itself); `exact h1` then sets `?m := b`. -/
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  apply Nat.lt_of_lt_of_le
  exact h1
  exact h2

/-! ### W2. Three ways to pass the same argument, side by side (R1, R2, R3) -/
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le (m := b) h1 h2
example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := @Nat.lt_of_lt_of_le _ b _ h1 h2

/-! ### W3. R5, R6, R7 chained on an involution `g` (`g (g x) = x` for every `x`)
`@hg a : g (g a) = a`; applying `g` twice to both sides (R6 twice) gives `g (g (g (g a))) = g (g a)`;
chaining (R7) with `@hg a` again ends at `a`. -/
example {α : Type} (g : α → α) (hg : ∀ {x : α}, g (g x) = x) (a : α) : g (g (g (g a))) = a := by
  have k1 := @hg a
  have k2 := congrArg g (congrArg g k1)
  exact k2.trans k1

end E023Guide
