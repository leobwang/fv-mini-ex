/- Guide for E013 (Max of two).
Part R: one reference entry per tactic, term or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`c : Prop` is a condition, `[Decidable c]` says Lean can compute whether `c` holds (so `if c` is allowed).
All entries use the guide's function `lowCap` below, NOT the exercise's.
Part W: worked combinations on `lowCap`.
Assumed: Lean basics up to E012, in particular `def` (E002), `exact` (E003), `∧`/`∨` (E005),
`simp [f]` (E010), `omega` (E011), `if-then-else` (E012).
-/

namespace E013Guide

/-- `x`, capped at `10` from above. -/
def lowCap (x : Int) : Int := if x ≤ 10 then x else 10

/-! # Part R · Reference entries -/

/-! ## Writing a function with a case distinction -/

/-! ### R1. `if c then x else y` · closes a `⊢ α` goal (a `def` body)
Both branches have the same type `α`. `if c` needs `[Decidable c]`; `a ≤ b`, `a < b`, `a = b` on `Int`
are decidable, so nothing extra is needed. In a `def` body you write the term directly after `:=`,
as in `lowCap` above. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) : α := by
  exact if c then x else y

/-! ## Splitting on the condition -/

/-! ### R2. `by_cases h : c` · goal list: one goal → two
`case pos` gets `h : c`, `case neg` gets `h : ¬c`; the goal itself is copied unchanged. Work on them in
order, or focus each with `·` (TACTIC_STATES, "Structure"). -/
example (c G : Prop) (h1 : c → G) (h2 : ¬c → G) : G := by
  by_cases h : c
  exact h1 h
  exact h2 h

/-! ## Removing the `if` with `simp` -/

/-! ### R3. `simp only [f]` · goal: the name `f x` → its body, an `if`
`simp [f]` does the same and then keeps simplifying. Without a fact about the condition it cannot pick
a branch, so the `if` stays (W2). -/
example (x : Int) (P : Int → Prop) (h : P (if x ≤ 10 then x else 10)) : P (lowCap x) := by
  simp only [lowCap]
  exact h

/-! ### R4. `simp [hc]` with `hc : c` · goal: `if c then x else y` → `x`
`simp` rewrites `c` to `True` using `hc`, then `if True then x else y` to `x` (lemma `if_pos`). -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hc : c) (h : P x) :
    P (if c then x else y) := by
  simp [hc]
  exact h

/-! ### R5. `simp [hc]` with `hc : ¬c` · goal: `if c then x else y` → `y`
`simp` rewrites `c` to `False` using `hc`, then `if False then x else y` to `y` (lemma `if_neg`). -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hc : ¬c) (h : P y) :
    P (if c then x else y) := by
  simp [hc]
  exact h

/-! ### R6. `simp [hc]` on a conjunction · goal: true parts removed, the rest left
`x ≤ x` becomes `True` (`le_refl`), `x = x` becomes `True`, so `y = x ∨ x = x` becomes `True`
(`or_true`), `c` becomes `True` via `hc`, and `True ∧ Q` becomes `Q` (`true_and`). Only `P` is left.
When every part is true, `simp` closes the goal. -/
example (c P : Prop) (x y : Int) (hc : c) (h : P) : P ∧ c ∧ x ≤ x ∧ (y = x ∨ x = x) := by
  simp [hc]
  exact h

/-! ### R7. `omega` with a negated comparison `h : ¬a ≤ b` · closes `b ≤ a`
On `Int`, `¬a ≤ b` means `b < a`; `omega` reads `¬`, `<`, `≤` in the context by itself (E011). -/
example (a b : Int) (h : ¬a ≤ b) : b ≤ a := by
  omega

/-! # Part W · Worked combinations (on `lowCap`, not the exercise's function) -/

/-! ### W1. `by_cases` on the `if`'s condition, then `simp [lowCap, h]` in each case (R2, R3–R6, R7)
In `case pos` the goal becomes `x ≤ x` and `simp` closes it; in `case neg` it becomes `10 ≤ x`, which
`simp` cannot finish but `omega` can, from `h : ¬x ≤ 10`. -/
example (x : Int) : lowCap x ≤ x := by
  by_cases h : x ≤ 10
  simp [lowCap, h]
  simp [lowCap, h]
  omega

/-! ### W2. Without `h`, `simp [lowCap]` unfolds but cannot choose a branch: the `if` stays -/
example (x : Int) (h : (if x ≤ 10 then x else 10) ≤ x) : lowCap x ≤ x := by
  simp [lowCap]
  exact h

end E013Guide
