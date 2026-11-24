/- Guide for E027 (simp lemmas).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The guide works on its own definitions `addTwo` and `thrice` (and `triple` in Part W), not on the
exercise's `twice` and `inc`.
Part W: worked combinations: a whole `simp` call, the same call step by step, dropping a simp lemma
with `simp [-l]`, and tagging a lemma after the fact with `attribute [simp]`.
Assumed: Lean basics up to E026, in particular `rfl` (E001), `def` (E002), `exact` (E003) and
`simp`, `simp only [l]`, `simp [f]` (E010).
-/

namespace E027Guide

/-- `addTwo n = n + 2`: our own definition, so plain `simp` does not unfold it (E010, R4). -/
def addTwo (n : Nat) : Nat := n + 2

/-- `thrice f x = f (f (f x))`: a definition that takes a function `f` as an argument. -/
def thrice (f : Nat → Nat) (x : Nat) : Nat := f (f (f x))

/-! # Part R · Reference entries -/

/-! ## Proving an equation by definition -/

/-! ### R1. `rfl` · goal `d a = (body of d at a)` closed: both sides are equal after unfolding `d`
`rfl` (E001) unfolds definitions while it compares the two sides. The term `:= rfl` and the tactic
`:= by rfl` prove the same equations. -/
example (n : Nat) : addTwo n = n + 2 := by
  rfl

/-! ## Tagging a lemma for `simp` -/

/-- R2: the defining equation of `addTwo`, proved by R1 and tagged `@[simp]`. -/
@[simp] theorem addTwo_eq (n : Nat) : addTwo n = n + 2 := rfl

/-! ### R2. `@[simp] theorem l … : lhs = rhs` · simp set gains `l`; every later plain `simp`
rewrites `lhs` → `rhs`
The tag changes no goal itself. It acts on every `simp` written after the declaration, in this file
and in files that import it: there `simp` now unfolds `addTwo` with no `[addTwo]` in brackets
(compare E010, R4). -/
example (k : Nat) (P : Nat → Prop) (h : P (k + 2)) : P (addTwo k) := by
  simp
  exact h

/-- R3: the defining equation of `thrice`; `f` is a variable of function type. -/
@[simp] theorem thrice_apply (f : Nat → Nat) (x : Nat) : thrice f x = f (f (f x)) := rfl

/-! ### R3. a simp lemma with a function variable · goal: `thrice g a` → `g (g (g a))`
In `thrice_apply` both `f` and `x` are variables, so the left side `thrice f x` matches `thrice`
applied to ANY function and ANY number: `f := g`, `x := a` here. It matches only when `thrice` has
both of its arguments: a bare `thrice g` (no `x`) is not rewritten. -/
example (g : Nat → Nat) (a : Nat) (P : Nat → Prop) (h : P (g (g (g a)))) : P (thrice g a) := by
  simp
  exact h

/-! ### R4. nested calls · goal: `thrice (thrice g) a` → nine `g`s; `simp` rewrites inside its own
results until nothing matches
The outer call matches R3 with `f := thrice g` (a partial application: `thrice` with its first
argument only). The result `thrice g (thrice g (thrice g a))` has three full calls `thrice g t`,
and `simp` rewrites each of them in turn. -/
example (g : Nat → Nat) (a : Nat) (P : Nat → Prop)
    (h : P (g (g (g (g (g (g (g (g (g a)))))))))) : P (thrice (thrice g) a) := by
  simp only [thrice_apply]
  exact h

/-! ## Closing the arithmetic -/

/-! ### R5. `simp` closes `k + 2 + 2 + 2 = k + 6` · goal closed
After the unfolding, what is left is an equation whose two sides differ only by numerals. `simp`
cancels the common summands (`Nat.add_right_cancel_iff : m + n = k + n ↔ m = k` and
`Nat.add_left_cancel_iff : n + m = n + k ↔ m = k`, E010 R10–R11) and closes it. -/
example (k : Nat) : k + 2 + 2 + 2 = k + 6 := by
  simp

/-! # Part W · Worked combinations (on `addTwo`, `thrice`, `triple`, not the exercise's objects) -/

/-! ### W1. One plain `simp` uses both tagged lemmas and finishes: R3, R2, R5 -/
example (n : Nat) : thrice addTwo n = n + 6 := by
  simp

/-! ### W2. The same rewriting, one lemma at a time: R3, then R2 -/
example (n : Nat) (P : Nat → Prop) (h : P (n + 2 + 2 + 2)) : P (thrice addTwo n) := by
  simp only [thrice_apply]
  simp only [addTwo_eq]
  exact h

/-! ### W3. `simp [-l]` drops the tagged lemma `l` for one call; `[addTwo]` unfolds the definition
instead. Both give `P (n + 2)` here. -/
example (n : Nat) (P : Nat → Prop) (h : P (n + 2)) : P (addTwo n) := by
  simp [-addTwo_eq, addTwo]
  exact h

/-! ### W4. `attribute [simp] l` tags an existing theorem after its declaration -/
def triple (n : Nat) : Nat := 3 * n

/-- Declared without the tag: plain `simp` does not know it yet. -/
theorem triple_eq (n : Nat) : triple n = 3 * n := rfl

attribute [simp] triple_eq

example (k : Nat) (P : Nat → Prop) (h : P (3 * k)) : P (triple k) := by
  simp
  exact h

end E027Guide
