/- Guide for E032 (Option-returning functions).
Part R: one reference entry per tactic, term or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G` is an arbitrary goal (a `Prop`) when the step does not look at the goal at all.
All entries use the guide's functions `safeSub` and `first?` below, NOT the exercise's.
Part W: worked combinations on `safeSub` and `dropTwo?`.
Assumed: Lean basics up to E031, in particular `rfl` (E001), `match` (E002), `intro`/`exact` (E003),
`⟨_, _⟩` (E004), `constructor` (E005), `rw` (E009), `simp [f]`/`simp at h` (E010), `omega` (E011),
`if-then-else` (E012), `by_cases` (E013), `Option` and its two constructors (E016).
-/

namespace E032Guide

/-- Subtraction that refuses to truncate: `none` when `a < b` (where `Nat` subtraction would give 0). -/
def safeSub (n k : Nat) : Option Nat := if n < k then none else some (n - k)

/-- The head of a list, if there is one. The first arm that matches wins; `_` matches anything. -/
def first? {α : Type} : List α → Option α := fun
  | x :: _ => some x
  | _ => none

/-! # Part R · Reference entries -/

/-! ## Writing a function that may fail -/

/-! ### R1. `if c then none else some x` · closes a `⊢ Option α` goal
`Option α` has exactly two kinds of values: `none` (no result) and `some x` with `x : α`. Both branches
of the `if` must have type `Option α`, so the success branch is wrapped in `some`. `if c` needs
`[Decidable c]`: Lean must be able to compute whether `c` holds. `b = 0` and `a < b` on `Nat` are
decidable, so nothing extra is needed there. In a `def` body you write the term directly after `:=`,
as in `safeSub` above. -/
example {α : Type} (c : Prop) [Decidable c] (x : α) : Option α := by
  exact if c then none else some x

/-! ### R2. `fun | pat₁ => e₁ | _ => e₂` (pattern-matching lambda) · closes a `⊢ List α → Option α` goal
`fun | … ` is `fun l => match l with | …`. Arms are tried top to bottom; the first pattern that fits
wins, so the catch-all `_` goes LAST. A pattern can look several elements deep: `x :: y :: rest`
matches every list with at least two elements. As in `first?` above, the body comes after `:= fun`
on the def line, one arm per line. -/
example {α : Type} : List α → Option α := by
  exact fun
    | x :: _ => some x
    | _ => none

/-! ## Proving what the function returns -/

/-! ### R3. `constructor` on `A ∧ B` · goal → two goals (`case left`, `case right`) -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  exact ha
  exact hb

/-! ### R4. `intro h` · goal `A → B` → context gains `h : A`, goal `B` -/
example (A B : Prop) (k : A → B) : A → B := by
  intro h
  exact k h

/-! ### R5. `simp [hc]` with `hc : c` · goal: `if c then x else y` → `x`
`simp` rewrites the condition `c` to `True` using `hc`, then `if True then x else y` to `x`.
Add the function's name to unfold it first: `simp [safeSub, hc]` (E010). If the result is an
equation whose sides agree, `simp` closes the goal. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hc : c) (h : P x) :
    P (if c then x else y) := by
  simp [hc]
  exact h

/-! ### R6. `simp [hc]` with `hc : ¬c` · goal: `if c then x else y` → `y`
`n ≠ 0` is notation for `¬(n = 0)`, so `hc : n ≠ 0` selects the `else` branch of `if n = 0`. -/
example {α : Type} (n : Nat) (x y : α) (P : α → Prop) (hc : n ≠ 0) (h : P y) :
    P (if n = 0 then x else y) := by
  simp [hc]
  exact h

/-! ## Using a hypothesis about the result -/

/-! ### R7. `by_cases hc : c` · goal list: one goal → two (`case pos` with `hc : c`, `case neg` with `hc : ¬c`) -/
example (c G : Prop) (h1 : c → G) (h2 : ¬c → G) : G := by
  by_cases hc : c
  exact h1 hc
  exact h2 hc

/-! ### R8. `simp at h` with `h : none = some q` · closes the goal
Different constructors are never equal, so `simp` turns `h` into `False`; a hypothesis `False` proves
any goal, and `simp at h` closes it right there. Any later tactic for that goal errors with "no goals". -/
example {α : Type} (q : α) (G : Prop) (h : none = some q) : G := by
  simp at h

/-! ### R9. `simp at h` with `h : some a = some b` · context: `h` becomes `a = b`
`some` is injective (lemma `Option.some.injEq`, which `simp` uses by itself). -/
example {α : Type} (a b : α) (G : Prop) (h : some a = some b) (k : a = b → G) : G := by
  simp at h
  exact k h

/-! ### R10. `rw [← h]` with `h : e = q` · goal: `q` → `e`
`←` uses `h` right to left: every `q` in the goal becomes `e`. -/
example (e q : Nat) (P : Nat → Prop) (h : e = q) (hp : P e) : P q := by
  rw [← h]
  exact hp

/-! ### R11. `Nat.div_mul_le_self` · closes `m / n * n ≤ m`
`Nat.div_mul_le_self : ∀ (m n : Nat), m / n * n ≤ m`. `/` on `Nat` rounds down, so multiplying back
never overshoots. It holds for `n = 0` too, since `m / 0 = 0` in Lean. -/
example (m n : Nat) : m / n * n ≤ m := by
  exact Nat.div_mul_le_self m n

/-! ## Evaluating on lists of a known shape -/

/-! ### R12. `exact ⟨ha, hb, hc⟩` · closes `A ∧ B ∧ C`
`∧` nests to the right (`A ∧ (B ∧ C)`), and `⟨_, _, _⟩` fills all three halves at once. -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : A ∧ B ∧ C := by
  exact ⟨ha, hb, hc⟩

/-! ### R13. `rfl` on a pattern-matching function · closes `f (x :: xs) = …`
When the argument's SHAPE is known (`[]`, `[x]`, `x :: y :: rest`), Lean picks the matching arm by
computation, even though `x`, `xs` are variables. So `rfl` closes the equation. -/
example (x : Nat) (xs : List Nat) : first? (x :: xs) = some x := by
  rfl

/-! # Part W · Worked combinations (on `safeSub` and `dropTwo?`, not the exercise's functions) -/

/-! ### W1. Unfold and decide the `if` in one call: R4, then R5 with the definition's name -/
example (a b : Nat) : a < b → safeSub a b = none := by
  intro h
  simp [safeSub, h]

/-! ### W2. Case split, then simplify the hypothesis in each case: R7, R5/R6 + R8 at `h`, R6 + R9 at `h` -/
example (a b r : Nat) (h : safeSub a b = some r) : r + b = a := by
  by_cases hab : a < b
  simp [safeSub, hab] at h
  simp [safeSub, hab] at h
  omega

/-- The list without its first two elements, if it has two. -/
def dropTwo? : List Nat → Option (List Nat) := fun
  | _ :: _ :: rest => some rest
  | _ => none

/-! ### W3. Three shapes, three `rfl`s, one triple (R12, R13) -/
example (x y : Nat) (rest : List Nat) :
    dropTwo? [] = none ∧ dropTwo? [x] = none ∧ dropTwo? (x :: y :: rest) = some rest := by
  exact ⟨rfl, rfl, rfl⟩

end E032Guide
